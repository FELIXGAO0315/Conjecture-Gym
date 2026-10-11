"""Graph-domain conjecture generator (PolyForge v1.1, stage 1).

Mirrors the hex pipeline — sample premises, enumerate candidate linear
(in)equalities among graph invariants, keep those that genuinely need integer
rounding or a case split, minimise premises, strengthen / drop redundant terms,
exactly re-check, regression-test on the real graph dataset, gate with an integer
counter-model over the active inventory, find the shortest proof, score, tag and
write.  Conclusions range over any invariant (both bounds); graph *properties*
appear only as premises.  The domain-agnostic flow (cache, renumber, record IO,
worker entry) is reused from ``PolyForge.generator.generator``.
"""

from __future__ import annotations

import json
import random
from collections import defaultdict
from datetime import datetime, timezone
from fractions import Fraction
from math import gcd, ceil as _ceil
import itertools as _it

import numpy as np
from scipy.optimize import linprog, milp, LinearConstraint, Bounds

from ...anvil import deducer as D
from ...anvil.deducer import Context, traceback, recheck
from . import inventory as INV
from . import deduction as DED
from . import formalizer as F
from ...scoring import iris as IRIS
from ...scoring import hardness as HARD
from ...generator import generator as CG
from ...generator.generator import (
    cached_context, _ctx_cache_clear, renumber_steps,
    _count_derivation_steps, _used_inventory, _primitive_int,
)

from pathlib import Path

ROOT = Path(__file__).resolve().parent
DATA = ROOT / "data" / "graph_pool.json"
RECORD = ROOT / "record"
LEAN_DIR = F.LEAN_DIR

GENERATOR_VERSION = "1.1.2"
MAIN_COEFFS = (1, 2)          # main-variable coefficient
OTHER_COEFFS = (-2, -1, 1, 2)  # other-term coefficients
MAX_COEFF = 6                 # guard on display coefficients
MAX_CONCLUSION_TERMS = 3      # terms besides the main variable
GROUP_WORK_BUDGET = 120000
RO_MAX_RATIO = CG.RO_MAX_RATIO
MAX_SHORTEN_ROUNDS = 1
LEMMA_LIB_MAX = 50
POOL_N_MAX = 7                # dataset covers n ≤ 7
_LP_TOL = 1e-7

VARS = list(DED.VARS)
_ALL_IDX = {v: i for i, v in enumerate(VARS)}
_NVARS = len(VARS)

# hardness parameters: which inventory names are "theorems" (heavier weight).
_HARD_INV_THEOREMS = tuple(e["name"] for e in INV.INVENTORY)


def _pdiff(tb):
    return HARD.proof_difficulty(tb, _HARD_INV_THEOREMS, ())


def _pstats(tb):
    return HARD.proof_structure_stats(tb, _HARD_INV_THEOREMS)


# ── properties ────────────────────────────────────────────────────────────────
# a numeric/param-free property, or a parametric one carrying a value.
PROP_SIMPLE = ["is_connected", "is_tree", "is_acyclic", "is_bipartite",
               "not_bipartite", "has_cycle", "nontrivial"]
PROP_PARAM = ["is_regular", "is_k_edge_connected"]


def property_closure(props: set) -> set:
    """Apply inventory implication rules to closure."""
    out = set(props)
    changed = True
    while changed:
        changed = False
        for ante, cons, _ in INV.IMPLICATIONS:
            if ante in out:
                for c in cons:
                    if c not in out:
                        out.add(c); changed = True
    # has_cycle ⟺ ¬ acyclic ; keep both consistent (don't auto-add, just record)
    return out


def dedup_properties(props):
    """§IV.1: drop a property premise implied by another (e.g. is_acyclic when
    is_tree is present; is_connected when is_tree; nontrivial when has_cycle)."""
    keep = []
    for i, p in enumerate(props):
        implied = False
        for j, q in enumerate(props):
            if i == j:
                continue
            if p["name"] in (property_closure({q["name"]}) - {q["name"]}):
                # p is implied by q; if mutual, keep the earlier one
                mutual = q["name"] in (property_closure({p["name"]}) - {p["name"]})
                if not mutual or j < i:
                    implied = True
                    break
        if not implied:
            keep.append(p)
    return keep


def finite_vars(props: set) -> set:
    """Variables usable (finite) given the properties present."""
    usable = set(v for v in VARS if v not in DED.FINITENESS)
    for v, need in DED.FINITENESS.items():
        if need in props:
            usable.add(v)
    return usable


# ── premise sampling (§III.3) ─────────────────────────────────────────────────
def sample_premises(rng: random.Random):
    """Return (property_premises, numeric_premises).  property_premises is a list
    of dicts {name, param?}; numeric_premises is a list of {coeffs, rel, rhs, text}."""
    props = []
    # 0–2 property premises, mutually consistent
    n_props = rng.randint(0, 2)
    pool = list(PROP_SIMPLE) + list(PROP_PARAM)
    rng.shuffle(pool)
    chosen = set()
    for name in pool:
        if len(props) >= n_props:
            break
        # consistency: don't take both acyclic & has_cycle, bipartite & not_bipartite
        if name == "has_cycle" and ("is_acyclic" in chosen or "is_tree" in chosen):
            continue
        if name == "is_acyclic" and "has_cycle" in chosen:
            continue
        if name == "is_bipartite" and "not_bipartite" in chosen:
            continue
        if name == "not_bipartite" and ("is_bipartite" in chosen or "is_tree" in chosen
                                        or "is_acyclic" in chosen):
            continue
        entry = {"name": name}
        if name == "is_regular":
            entry["param"] = rng.randint(0, 3)
        elif name == "is_k_edge_connected":
            entry["param"] = rng.randint(1, 3)
        props.append(entry)
        chosen.add(name)
    pset = property_closure(chosen)
    usable = finite_vars(pset)

    # 1–2 numeric premises over usable variables
    numeric = []
    n_num = rng.randint(1, 2)
    uvars = sorted(usable)

    def bound():
        v = rng.choice(uvars)
        rel = rng.choice([">=", "<="])
        c = rng.randint(1, 6)
        return {"coeffs": {v: 1}, "rel": rel, "rhs": c, "text": f"{v} {rel} {c}"}

    def relation():
        # §II: two-variable relations only x≤y, x≥y, x≤2y, x≥2y
        if len(uvars) < 2:
            return bound()
        x, y = rng.sample(uvars, 2)
        rel = rng.choice([">=", "<="])
        mult = rng.choice([1, 2])
        rhs_txt = y if mult == 1 else f"{mult}*{y}"
        return {"coeffs": {x: 1, y: -mult}, "rel": rel, "rhs": 0,
                "text": f"{x} {rel} {rhs_txt}"}

    makers = [bound, bound, relation]
    for _ in range(n_num):
        numeric.append(rng.choice(makers)())
    return props, numeric


def _prop_names(props):
    return [p["name"] for p in props]


def _prop_params(props):
    return {p["name"]: p["param"] for p in props if "param" in p}


# ── numeric-premise de-duplication (§III.3) ───────────────────────────────────
def _prim(coeffs, const):
    return D._primitive(coeffs, const)


def dedup_numeric(premises):
    keep = []
    seen = set()
    for pr in premises:
        prim = _prim({v: Fraction(c) for v, c in pr["coeffs"].items()}, Fraction(-pr["rhs"]))
        key = (tuple(sorted(prim[0].items())) if prim else (), pr["rel"], str(pr["rhs"]))
        if key not in seen:
            seen.add(key)
            keep.append(pr)
    return keep


def _premise_implies(a, b):
    ca = {v: Fraction(c) for v, c in a["coeffs"].items()}
    cb = {v: Fraction(c) for v, c in b["coeffs"].items()}
    pa, pb = _prim(ca, Fraction(-a["rhs"])), _prim(cb, Fraction(-b["rhs"]))
    if pa is None or pb is None:
        return False
    ia, na = pa
    ib, nb = pb
    if a["rel"] == b["rel"] == ">=" and tuple(sorted(ia.items())) == tuple(sorted(ib.items())):
        return -na >= -nb
    if a["rel"] == b["rel"] == "<=" and tuple(sorted(ia.items())) == tuple(sorted(ib.items())):
        return na >= nb
    return False


def minimize_numeric_redundant(premises):
    keep = list(premises)
    changed = True
    while changed:
        changed = False
        for i, b in enumerate(keep):
            for j, a in enumerate(keep):
                if i == j:
                    continue
                if _premise_implies(a, b) and not (_premise_implies(b, a) and j > i):
                    del keep[i]; changed = True; break
            if changed:
                break
    return keep


# ── LP machinery over the active inventory ────────────────────────────────────
def _conc_form(conc):
    return D._conc_to_form(conc)


def _unconditional_forms():
    forms = []
    for e in DED.INVENTORY:
        forms.append(_conc_form(e["conclusion"]))
    return forms


def _premise_forms(premises):
    return [_conc_form(pr) for pr in premises]


def _prep(constraints):
    A_ub, b_ub, A_eq, b_eq = [], [], [], []
    for coeffs, const, rel in constraints:
        row = [0.0] * _NVARS
        for v, c in coeffs.items():
            row[_ALL_IDX[v]] = float(c)
        if rel == "==":
            A_eq.append(row); b_eq.append(-float(const))
        else:
            A_ub.append([-x for x in row]); b_ub.append(float(const))
    return (np.array(A_ub) if A_ub else None, np.array(b_ub) if b_ub else None,
            np.array(A_eq) if A_eq else None, np.array(b_eq) if b_eq else None)


def _lp(cvec, mats):
    A_ub, b_ub, A_eq, b_eq = mats
    D.work_tick()
    try:
        res = linprog(cvec, A_ub=A_ub, b_ub=b_ub, A_eq=A_eq, b_eq=b_eq,
                      bounds=[(None, None)] * _NVARS, method="highs")
    except Exception:
        return ("infeasible", None, None)
    if res.status == 0 and np.isfinite(res.fun):
        return ("opt", float(res.fun), {v: float(res.x[_ALL_IDX[v]]) for v in VARS})
    if res.status == 3:
        return ("unbounded", None, None)
    return ("infeasible", None, None)


def _cvec(direction):
    c = [0.0] * _NVARS
    for v, coef in direction.items():
        c[_ALL_IDX[v]] = float(coef)
    return c


def _triggerable_conditionals(constraints):
    out = []
    for e in DED.CONDITIONAL_THEOREMS:
        h = e["hypothesis"]
        coeffs = {v: Fraction(c) for v, c in h["coeffs"].items()}
        st, v, _ = _lp(_cvec(coeffs), _prep(constraints))
        if st == "opt" and v - float(h["rhs"]) >= -_LP_TOL:
            out.append(_conc_form(e["conclusion"]))
    return out


def _build_split_tree(prem_forms, assum_forms, depth):
    base = prem_forms + assum_forms + _unconditional_forms()
    leaf = base + _triggerable_conditionals(base)
    node = {"mats": _prep(leaf), "splits": []}
    if depth > 0:
        for _label, expr, ths in [(l, {v: Fraction(c) for v, c in e.items()}, t)
                                  for l, e, t in DED.SPLIT_SPECS]:
            for c in ths:
                st1, v1, _ = _lp(_cvec(expr), _prep(base))
                if st1 == "opt" and v1 - float(c) >= -_LP_TOL:
                    continue
                neg = {v: -x for v, x in expr.items()}
                st2, v2, _ = _lp(_cvec(neg), _prep(base))
                if st2 == "opt" and v2 - float(-(c - 1)) >= -_LP_TOL:
                    continue
                ge = _build_split_tree(prem_forms, assum_forms + [(dict(expr), Fraction(-c), ">=")], depth - 1)
                le = _build_split_tree(prem_forms, assum_forms + [({v: -x for v, x in expr.items()}, Fraction(c - 1), ">=")], depth - 1)
                node["splits"].append((ge, le))
    return node


def _merge(rge, rle):
    if rge[0] == "unbounded" or rle[0] == "unbounded":
        return None
    feas = [r[1] for r in (rge, rle) if r[0] == "opt"]
    return min(feas) if feas else None


def _vint(node, cvec, depth):
    st, val, xstar = _lp(cvec, node["mats"])
    if st == "unbounded":
        return ("unbounded", None)
    if st != "opt":
        return ("infeasible", None)
    best = _ceil(val - _LP_TOL)
    if depth > 0:
        for ge, le in node["splits"]:
            rge = _vint(ge, cvec, depth - 1)
            rle = _vint(le, cvec, depth - 1)
            mv = _merge(rge, rle)
            if mv is not None and mv > best:
                best = mv
        pick = D._bnb_pick_var(xstar)
        if pick is not None:
            var, fl = pick
            ge = {"mats": _add_bound(node["mats"], var, ">=", fl + 1), "splits": []}
            le = {"mats": _add_bound(node["mats"], var, "<=", fl), "splits": []}
            rge = _vint(ge, cvec, depth - 1)
            rle = _vint(le, cvec, depth - 1)
            mv = _merge(rge, rle)
            if mv is not None and mv > best:
                best = mv
    return ("opt", best)


def _add_bound(mats, var, rel, k):
    A_ub, b_ub, A_eq, b_eq = mats
    row = np.zeros(_NVARS)
    if rel == "<=":
        row[_ALL_IDX[var]] = 1.0; b = float(k)
    else:
        row[_ALL_IDX[var]] = -1.0; b = -float(k)
    nA = np.vstack([A_ub, row]) if A_ub is not None else row.reshape(1, -1)
    nb = np.concatenate([b_ub, [b]]) if b_ub is not None else np.array([b])
    return (nA, nb, A_eq, b_eq)


def linearly_derivable(premises, conclusion):
    base = _premise_forms(premises) + _unconditional_forms()
    base += _triggerable_conditionals(base)
    coeffs = {v: Fraction(c) for v, c in conclusion["coeffs"].items()}
    st, v, _ = _lp(_cvec(coeffs), _prep(base))
    if st != "opt":
        return False
    return v - float(conclusion["rhs"]) >= -_LP_TOL


def classify_depth(premises, direction):
    pf = _premise_forms(premises)
    lin = pf + _unconditional_forms()
    lin += _triggerable_conditionals(lin)
    cvec = _cvec({v: int(c) for v, c in direction.items()})
    slin, vlin, _ = _lp(cvec, _prep(lin))
    tree = _build_split_tree(pf, [], D.DEFAULT_SPLIT_DEPTH)
    sint, vint = _vint(tree, cvec, D.DEFAULT_SPLIT_DEPTH)
    if sint != "opt" or slin != "opt":
        return "split_needed"
    return "rounding_only" if vint == _ceil(vlin - _LP_TOL) else "split_needed"


# ── direction / candidate enumeration (§III.4) ────────────────────────────────
def _coprime(d):
    vals = [abs(int(c)) for c in d.values() if int(c) != 0]
    if not vals:
        return {}
    g = 0
    for v in vals:
        g = gcd(g, v)
    g = g or 1
    return {k: int(c) // g for k, c in d.items() if int(c) != 0}


def choose_primary(seed, usable):
    """§III: deterministically rotate the primary variable per premise set (by the
    per-set seed), among the finiteness-valid variables, in fixed VARS order."""
    uorder = [v for v in VARS if v in usable]
    if not uorder:
        return None
    start = seed % len(uorder)
    return uorder[start]


def enumerate_directions(usable, main):
    """§III.2: directions with THE given primary variable (coeff 1 or 2) plus up to
    2 other usable variables (coeff |·| ≤ 2); both signs (upper and lower bounds)."""
    seen, dirs = set(), []
    others = [v for v in sorted(usable) if v != main]

    def add(d):
        d = _coprime(d)
        if not d or d.get(main, 0) == 0:
            return
        key = tuple(sorted(d.items()))
        if key in seen:
            return
        seen.add(key); dirs.append(d)

    for a in MAIN_COEFFS:
        base = {main: a}
        add(dict(base))
        for v in others:
            for c in OTHER_COEFFS:
                add(dict(base, **{v: c}))
        for v1, v2 in _it.combinations(others, 2):
            for c1 in OTHER_COEFFS:
                for c2 in OTHER_COEFFS:
                    add(dict(base, **{v1: c1, v2: c2}))
    for d in list(dirs):
        add({v: -c for v, c in d.items()})
    return dirs


def enumerate_candidates(premises, usable, main, stats, rng, accept):
    pf = _premise_forms(premises)
    lin = pf + _unconditional_forms()
    lin += _triggerable_conditionals(lin)
    lin_mats = _prep(lin)
    tree = _build_split_tree(pf, [], D.DEFAULT_SPLIT_DEPTH)
    directions = enumerate_directions(usable, main)
    rng.shuffle(directions)
    stats["directions_total"] += len(directions)
    out = []
    for d in directions:
        cvec = _cvec(d)
        slin, vlin, _ = _lp(cvec, lin_mats)
        if slin != "opt":
            continue
        sint, vint = _vint(tree, cvec, D.DEFAULT_SPLIT_DEPTH)
        if sint != "opt":
            continue
        if vint > vlin + _LP_TOL:
            dtype = "rounding_only" if vint == _ceil(vlin - _LP_TOL) else "split_needed"
            if dtype != accept:
                stats["rounding_only_skipped" if dtype == "rounding_only"
                      else "split_needed_skipped"] += 1
                continue
            out.append({"coeffs": dict(d), "rel": ">=", "rhs": int(vint)})
        else:
            stats["linear_only"] += 1
    # dedup to best bound per primitive LHS, apply coeff guard
    best = {}
    for cand in out:
        prim = _prim({v: Fraction(c) for v, c in cand["coeffs"].items()}, Fraction(-cand["rhs"]))
        if prim is None or prim[1].denominator != 1:
            continue
        ic = {v: int(x) for v, x in prim[0].items()}
        rhs = int(-prim[1])
        if any(abs(c) > MAX_COEFF for c in ic.values()):
            continue
        key = tuple(sorted(ic.items()))
        if key not in best or rhs > best[key]["rhs"]:
            best[key] = {"coeffs": ic, "rel": ">=", "rhs": rhs}
    return list(best.values())


# ── strengthen + drop redundant terms (§III.5) ────────────────────────────────
def _find_fact(ctx, conclusion):
    target = {v: Fraction(c) for v, c in conclusion["coeffs"].items()}
    pt = _prim(target, Fraction(-conclusion["rhs"]))
    if pt is None:
        return None
    it, nt = pt
    key = tuple(sorted((v, int(c)) for v, c in it.items()))
    best = None
    for f in ctx.all_prop_facts():
        pp = _prim(f.coeffs, f.const)
        if pp is None or pp[1].denominator != 1:
            continue
        if tuple(sorted((v, int(c)) for v, c in pp[0].items())) == key and -pp[1] >= -nt:
            if best is None or -pp[1] > -best[1]:
                best = (f, pp[1])
    return best[0] if best else None


def _strongest_in(ctx, direction):
    Ld = {v: int(c) for v, c in direction.items() if int(c) != 0}
    if not Ld:
        return None
    f = _find_fact(ctx, {"coeffs": Ld, "rel": ">=", "rhs": -10 ** 9})
    if f is None:
        return None
    prim = _primitive_int(f.coeffs, f.const)
    if prim is None or prim[1].denominator != 1:
        return None
    ic, nc = prim
    return {"coeffs": ic, "rel": ">=", "rhs": int(-nc)}, f


def _neg(d):
    return {v: -int(c) for v, c in d.items() if int(c) != 0}


def strengthen_and_simplify(conclusion0, premises, main_var, use_lemmas=True):
    d0 = {v: int(c) for v, c in conclusion0["coeffs"].items() if int(c) != 0}
    dirs = [d0, _neg(d0)]
    for x in [v for v in d0 if v != main_var]:
        red = {v: c for v, c in d0.items() if v != x}
        if main_var in red:
            dirs += [red, _neg(red)]
    ctx = cached_context(premises, dirs, use_lemmas=use_lemmas)
    r = _strongest_in(ctx, conclusion0["coeffs"])
    if r is None:
        return None
    cur, fact = r
    changed = True
    while changed:
        changed = False
        for x in [v for v in cur["coeffs"] if v != main_var]:
            reduced = {v: c for v, c in cur["coeffs"].items() if v != x}
            if main_var not in reduced:
                continue
            rr = _strongest_in(ctx, reduced)
            if rr is None:
                continue
            red_concl, rfact = rr
            # reduced implies cur using only non-negativity? keep if provable & not weaker
            if red_concl["rhs"] >= cur["rhs"] - 0 and set(red_concl["coeffs"]) <= set(cur["coeffs"]):
                cur, fact = red_concl, rfact
                changed = True
                break
    return cur, ctx, fact


# ── shortest proof (§III.6) ───────────────────────────────────────────────────
_SHORTEN_CONFIGS = [(0, False, False), (1, True, False), (1, False, True),
                    (1, True, True), (2, True, True)]


def _reprove(premises, conclusion, depth, uc, ub, use_lemmas=True):
    d0 = {v: int(c) for v, c in conclusion["coeffs"].items() if int(c) != 0}
    if not d0:
        return None
    ctx = Context(premises=premises, depth=depth, extra_directions=[d0, _neg(d0)],
                  use_conditional_split=uc, use_bnb=ub, use_lemmas=use_lemmas)
    ctx.saturate()
    fact = _find_fact(ctx, conclusion)
    if fact is None:
        return None
    tb = traceback(ctx, fact)
    return ctx, fact, tb, _pdiff(tb)


def shortest_lemma_free(premises, conclusion):
    best = None
    for depth, uc, ub in _SHORTEN_CONFIGS + [(D.DEFAULT_SPLIT_DEPTH, True, True)]:
        try:
            r = _reprove(premises, conclusion, depth, uc, ub, use_lemmas=False)
        except D.WorkBudgetExceeded:
            break
        if r is None:
            continue
        if best is None or r[3] < best[3]:
            best = r
    return best


def shorten_proof(premises, conclusion, tb, ctx, fact, init_cost, use_lemmas=True):
    best = (tb, ctx, fact, init_cost)
    if _pstats(tb)["case_splits"] == 0:
        return best[0], best[1], best[2], best[3], 0
    rounds = 0
    try:
        for _ in range(MAX_SHORTEN_ROUNDS):
            improved = False
            for depth, uc, ub in _SHORTEN_CONFIGS:
                r = _reprove(premises, conclusion, depth, uc, ub, use_lemmas=use_lemmas)
                if r is None:
                    continue
                if r[3] < best[3]:
                    best = (r[2], r[0], r[1], r[3]); improved = True
            if improved:
                rounds += 1
            else:
                break
    except D.WorkBudgetExceeded:
        pass
    return best[0], best[1], best[2], best[3], rounds


# ── integer counter-model gate (§III.6) ───────────────────────────────────────
_CM_N = _NVARS + len(DED.VARS)  # placeholder; rebuilt per set below


def counter_model(premises, conclusion):
    """Integer point satisfying premises + active inventory + ¬conclusion ⇒ bug."""
    ncond = len(DED.CONDITIONAL_THEOREMS)
    n = _NVARS + ncond
    idx = dict(_ALL_IDX)
    bigM = 10 ** 7
    cons = []

    def row(d):
        r = [0.0] * n
        for k, v in d.items():
            r[idx[k]] += float(v)
        return r

    for e in DED.INVENTORY:
        co, k, rel = _conc_form(e["conclusion"])
        rr = row(co)
        if rel == "==":
            cons.append((rr, -float(k), -float(k)))
        else:
            cons.append(([-x for x in rr], None, float(k)))
    for bi, e in enumerate(DED.CONDITIONAL_THEOREMS):
        b = _NVARS + bi
        hyp_rhs = float(e["hypothesis"]["rhs"])
        hyp_lhs = {v: Fraction(c) for v, c in e["hypothesis"]["coeffs"].items()}
        rr = row(hyp_lhs); rr[b] = bigM
        cons.append((rr, None, (hyp_rhs - 1) + bigM))
        cco, cck, crel = _conc_form(e["conclusion"])
        rr = row(cco); rr[b] = bigM
        cons.append((rr, -float(cck), None))          # conclusion ≥ (active when b=0)
        if crel == "==":                               # equality conditional: model ≤ too
            rr2 = row(cco); rr2[b] = -bigM
            cons.append((rr2, None, -float(cck)))
    for pr in premises:
        rr = row(pr["coeffs"]); rhs = float(pr["rhs"])
        if pr["rel"] == "=":
            cons.append((rr, rhs, rhs))
        elif pr["rel"] == ">=":
            cons.append((rr, rhs, None))
        else:
            cons.append((rr, None, rhs))
    rr = row({v: Fraction(c) for v, c in conclusion["coeffs"].items()})
    rhs = float(conclusion["rhs"])
    if conclusion["rel"] == ">=":
        cons.append((rr, None, rhs - 1))
    else:
        cons.append((rr, rhs + 1, None))
    A = np.array([c[0] for c in cons])
    lb = np.array([-np.inf if c[1] is None else c[1] for c in cons])
    ub = np.array([np.inf if c[2] is None else c[2] for c in cons])
    bl = np.array([0.0] * n)
    bu = np.array([1.0 if i >= _NVARS else 10 ** 5 for i in range(n)])
    D.work_tick()
    try:
        res = milp(c=np.zeros(n), constraints=[LinearConstraint(A, lb, ub)],
                   integrality=np.ones(n), bounds=Bounds(bl, bu))
    except Exception:
        return None
    if not (res is not None and res.success and res.x is not None):
        return None
    model = {v: int(round(res.x[idx[v]])) for v in VARS}

    # Exact verification (§III.6 gate must be precise): the big-M MILP can return a
    # numerically-infeasible point.  Accept ``model`` as a genuine counter-model only
    # if it exactly satisfies every premise and every active inventory fact (honouring
    # the conditional-theorem implications) while violating the conclusion; otherwise
    # it is a numerical artifact and there is no counter-model here.
    def _sat(co, rel, rhs):
        lhs = sum(Fraction(c) * model[v] for v, c in co.items())
        rhs = Fraction(rhs)
        if rel in ("=", "=="):
            return lhs == rhs
        if rel == ">=":
            return lhs >= rhs
        return lhs <= rhs
    for pr in premises:
        if not _sat(pr["coeffs"], pr["rel"], pr["rhs"]):
            return None
    for e in DED.INVENTORY:
        c = e["conclusion"]
        if not _sat(c["coeffs"], c["rel"], c["rhs"]):
            return None
    for e in DED.CONDITIONAL_THEOREMS:
        hyp = e["hypothesis"]
        if _sat(hyp["coeffs"], hyp["rel"], hyp["rhs"]):      # hypothesis holds → conclusion must
            c = e["conclusion"]
            if not _sat(c["coeffs"], c["rel"], c["rhs"]):
                return None
    if _sat(conclusion["coeffs"], conclusion["rel"], conclusion["rhs"]):
        return None                                          # conclusion holds → not a counter-model
    return model
    return None


# ── hashing / skeleton (§III.6) ───────────────────────────────────────────────
def _skel_lhs(coeffs):
    nz = {v: Fraction(c) for v, c in coeffs.items() if Fraction(c) != 0}
    prim = _prim(nz, Fraction(0))
    if prim is None:
        return ()
    return tuple(sorted((v, int(c)) for v, c in prim[0].items()))


def premise_key(props, numeric):
    items = []
    for pr in numeric:
        prim = _prim({v: Fraction(c) for v, c in pr["coeffs"].items()}, Fraction(-pr["rhs"]))
        key = (tuple(sorted((v, int(c)) for v, c in prim[0].items())) if prim else (),
               str(pr["rhs"]), pr["rel"])
        items.append(key)
    pk = frozenset((p["name"], p.get("param")) for p in props)
    return (frozenset(items), pk)


def conjecture_hash(props, numeric, conclusion):
    prim = _prim({v: Fraction(c) for v, c in conclusion["coeffs"].items()}, Fraction(-conclusion["rhs"]))
    ck = (tuple(sorted((v, int(c)) for v, c in prim[0].items())) if prim else (),
          conclusion["rel"], str(prim[1]) if prim else str(conclusion["rhs"]))
    return (premise_key(props, numeric), ck)


def conjecture_skeleton(props, numeric, conclusion):
    prem = frozenset((p["name"],) for p in props)
    num = frozenset((_skel_lhs(pr["coeffs"]), pr["rel"], "0" if pr["rel"] == "=" else "*")
                    for pr in numeric)
    con = (_skel_lhs(conclusion["coeffs"]), conclusion["rel"])
    return (prem, num, con)


def skeleton_better(new, old):
    rank = lambda a: 1 if a == "yes" else 0
    if rank(new["attained"]) != rank(old["attained"]):
        return rank(new["attained"]) > rank(old["attained"])
    if new["attained"] == "yes":
        if (new["touch"] or 0) != (old["touch"] or 0):
            return (new["touch"] or 0) > (old["touch"] or 0)
    return new["hardness"] > old["hardness"]


# ── rendering (§IV / §VII: primary on its own side) ──────────────────────────
_REL_SYM = {">=": ">=", "<=": "<=", "=": "="}


def _render_ineq(coeffs, rel, rhs):
    parts = []
    for v in VARS:
        c = int(coeffs.get(v, 0))
        if c == 0:
            continue
        parts.append(v if c == 1 else (f"-{v}" if c == -1 else f"{c}*{v}"))
    lhs = " + ".join(parts).replace("+ -", "- ") if parts else "0"
    return f"{lhs} {_REL_SYM[rel]} {rhs}"


def _display_premise(pr):
    """§IV.2: render a numeric premise with its coefficient-1 subject variable on
    the left (positive), e.g. ``tau <= omega`` / ``chi <= 2*max_deg`` / ``n >= 3``."""
    coeffs = {v: int(c) for v, c in pr["coeffs"].items() if int(c) != 0}
    rel, rhs = pr["rel"], int(pr["rhs"])
    subj = next((v for v in VARS if coeffs.get(v, 0) == 1), None)
    if subj is None:
        subj = next((v for v in VARS if coeffs.get(v, 0) > 0), None)
    if subj is None:
        return _render_ineq(coeffs, rel, rhs)
    a = coeffs[subj]
    left = subj if a == 1 else f"{a}*{subj}"
    rest = {v: -coeffs[v] for v in coeffs if v != subj}
    parts = []
    for v in VARS:
        rc = int(rest.get(v, 0))
        if rc == 0:
            continue
        parts.append(v if rc == 1 else (f"-{v}" if rc == -1 else f"{rc}*{v}"))
    if rhs != 0 or not parts:
        parts.append(str(rhs))
    rs = " + ".join(parts).replace("+ -", "- ")
    return f"{left} {rel} {rs}"


def _premise_text(pr):
    return f"({_display_premise(pr)})"


def display_conclusion(conclusion, primary):
    """§VII: orient the (internal ``>=``) conclusion so ``primary`` is alone on the
    left with a positive coefficient.  Returns ``(disp, primary)`` where ``disp`` is
    the full linear form ``{coeffs, rel, rhs}`` with ``primary`` positive (used for
    the JSON conclusion, the Lean goal, and property tagging); if ``primary`` was
    dropped in simplification, falls back to a remaining coefficient-1 variable."""
    L = {v: int(c) for v, c in conclusion["coeffs"].items() if int(c) != 0}
    c = int(conclusion["rhs"])
    if primary is None or L.get(primary, 0) == 0:
        primary = next((v for v in VARS if L.get(v, 0) == 1), None) or _main_var(L)
    a = L.get(primary, 0) if primary else 0
    if a >= 0:
        return {"coeffs": L, "rel": conclusion["rel"], "rhs": c}, primary
    return ({"coeffs": {v: -x for v, x in L.items()},
             "rel": "<=" if conclusion["rel"] == ">=" else ">=", "rhs": -c}, primary)


def _render_isolated(disp, primary):
    """Render ``a*primary REL (rest + rhs)`` with the primary variable alone left."""
    coeffs = disp["coeffs"]
    rhs = int(disp["rhs"])
    a = int(coeffs[primary])
    left = primary if a == 1 else f"{a}*{primary}"
    rest = {v: -int(coeffs[v]) for v in coeffs if v != primary and int(coeffs[v]) != 0}
    parts = []
    for v in VARS:
        rc = int(rest.get(v, 0))
        if rc == 0:
            continue
        parts.append(v if rc == 1 else (f"-{v}" if rc == -1 else f"{rc}*{v}"))
    if rhs != 0 or not parts:
        parts.append(str(rhs))
    rs = " + ".join(parts).replace("+ -", "- ")
    return f"{left} {disp['rel']} {rs}"


def formula_string(props, numeric, conclusion, primary):
    conds = [f"({p['name']}" + (f"({p['param']})" if 'param' in p else "") + ")" for p in props]
    conds += [_premise_text(pr) for pr in numeric]
    body = " and ".join(conds) if conds else "(true)"
    disp, prim = display_conclusion(conclusion, primary)
    return f"if ({body}), then ({_render_isolated(disp, prim)})"


def natural_language(props, numeric, conclusion, primary):
    prem = []
    for p in props:
        prem.append(p['name'] + (f"({p['param']})" if 'param' in p else ""))
    for pr in numeric:
        prem.append(_display_premise(pr))
    intro = ("Let G be a finite simple graph with the usual invariants "
             "(n, m, max_deg, min_deg, chi, omega, alpha, tau, diam, radius, girth).")
    disp, prim = display_conclusion(conclusion, primary)
    concl = _render_isolated(disp, prim)
    if prem:
        return f"{intro} Suppose {', '.join(prem)}. Then {concl}."
    return f"{intro} Then {concl}."


# ── conclusion_property tag (§IV.2) ───────────────────────────────────────────
def conclusion_property(props, disp):
    """Identify whether the (display-oriented) conclusion is equivalent to a known
    property.  ``disp`` is the primary-positive full form {coeffs, rel, rhs}."""
    c = {v: int(x) for v, x in disp["coeffs"].items()}
    rel, rhs = disp["rel"], int(disp["rhs"])
    # single-variable chi bounds
    if set(c) == {"chi"} and c["chi"] == 1:
        if rel == "<=" and rhs == 2:
            return "is_bipartite"
        if rel == "<=" and rhs == 1:
            return "edgeless"
        if rel == ">=" and rhs == 3:
            return "not_bipartite"
    # max_deg = min_deg  (max_deg - min_deg <= 0, with nonneg the reverse holds) → regular
    if set(c) == {"max_deg", "min_deg"} and rel == "<=" and rhs == 0 \
            and c.get("max_deg") == 1 and c.get("min_deg") == -1:
        return "is_regular"
    # m = n - 1 under is_connected → is_tree  (m - n <= -1)
    if "is_connected" in {p["name"] for p in props} and set(c) == {"m", "n"} \
            and c.get("m") == 1 and c.get("n") == -1 and rel == "<=" and rhs == -1:
        return "is_tree"
    return None


def _is_trivial(coeffs, rhs):
    if coeffs and all(c >= 0 for c in coeffs.values()) and rhs <= 0:
        return True
    if coeffs and all(c <= 0 for c in coeffs.values()) and rhs >= 0:
        return True
    return False


# ── real-dataset checks (§III.7) ──────────────────────────────────────────────
def _props_hold(gprops: dict, props) -> bool:
    for p in props:
        name = p["name"]
        if name == "is_regular":
            if not (gprops["is_regular"] and p.get("param") is not None):
                return False
            # param must match the graph's regular degree
        elif name == "is_k_edge_connected":
            pass  # handled numerically by edge_connectivity bound below
        else:
            if not gprops.get(name, False):
                return False
    return True


def pool_covered(props, numeric):
    """False iff some numeric premise forces n ≥ c with c > 7 (no pool witness)."""
    for pr in numeric:
        supp = [v for v, c in pr["coeffs"].items() if c]
        if supp == ["n"] and pr["rel"] == ">=" and \
                Fraction(pr["rhs"]) / Fraction(pr["coeffs"]["n"]) > POOL_N_MAX:
            return False
    return True


def _graph_matches(g, gprops, props, numeric):
    # property premises
    for p in props:
        name = p["name"]
        if name == "is_regular":
            if not g["regular"] or g["regular_degree"] != p.get("param"):
                return False
        elif name == "is_k_edge_connected":
            if g["edge_connectivity"] < p.get("param", 0):
                return False
        else:
            if not gprops.get(name, False):
                return False
    # numeric premises
    vals = DED.vars_from_graph(g)
    for pr in numeric:
        lhs = sum(Fraction(c) * (vals[v] if vals[v] is not None else 0)
                  for v, c in pr["coeffs"].items())
        rhs = Fraction(pr["rhs"])
        if pr["rel"] == "=" and lhs != rhs:
            return False
        if pr["rel"] == ">=" and lhs < rhs:
            return False
        if pr["rel"] == "<=" and lhs > rhs:
            return False
    return True


def dataset_subset(pool, props, numeric):
    out = []
    for g in pool:
        gp = INV.properties_of(g)
        if _graph_matches(g, gp, props, numeric):
            out.append(g)
    return out


def soundness_check(props, numeric, conclusion, pool):
    ccoeffs = {v: Fraction(c) for v, c in conclusion["coeffs"].items()}
    crhs = Fraction(conclusion["rhs"])
    for g in dataset_subset(pool, props, numeric):
        vals = DED.vars_from_graph(g)
        lhs = sum(c * vals[v] for v, c in ccoeffs.items())
        ok = lhs >= crhs if conclusion["rel"] == ">=" else lhs <= crhs
        if not ok:
            raise AssertionError(
                f"SOUNDNESS VIOLATION: graph atlas#{g.get('atlas_index')} "
                f"props={props} numeric={numeric} conclusion={conclusion} lhs={lhs} rhs={crhs}")


def iris_feature_vars(props, numeric, conclusion):
    """The variables the conjecture mentions that are finite on the subset."""
    used = set(conclusion["coeffs"])
    for pr in numeric:
        used |= set(pr["coeffs"])
    usable = finite_vars(property_closure({p["name"] for p in props}))
    return [v for v in VARS if v in used and v in usable]


# ── decomposability filter (§IV) ──────────────────────────────────────────────
def is_decomposable(premises, conclusion):
    """True if the conclusion L ≥ c splits into two non-empty groups A, B whose
    strongest provable bounds (using FULL deduction power — splits, B&B, rounding)
    satisfy b_A + b_B ≥ c.  Conclusions are internal ``>=`` forms."""
    L = {v: int(c) for v, c in conclusion["coeffs"].items() if int(c) != 0}
    c = int(conclusion["rhs"])
    terms = list(L)
    if len(terms) < 2:
        return False
    parts, seen = [], set()
    for r in range(1, len(terms)):
        for A in _it.combinations(terms, r):
            Aset = frozenset(A); Bset = frozenset(terms) - Aset
            key = frozenset((Aset, Bset))
            if key in seen:
                continue
            seen.add(key); parts.append((Aset, Bset))
    dirs = []
    for Aset, Bset in parts:
        for S in (Aset, Bset):
            d = {v: L[v] for v in S}
            dirs.append(d); dirs.append(_neg(d))
    ctx = cached_context(premises, dirs)            # full power (depth 3 + split + B&B)

    def bnd(S):
        # bound on the part L_S *as written* (keeping its original coefficients).
        # _strongest_in returns the bound on the coprime/primitive direction, so
        # scale it back by the gcd that was divided out (v1.1.2 §III.2 fix).
        d = {v: L[v] for v in S}
        r = _strongest_in(ctx, d)
        if r is None:
            return None
        g = 0
        for cc in d.values():
            g = gcd(g, abs(int(cc)))
        g = g or 1
        return g * r[0]["rhs"]

    for Aset, Bset in parts:
        bA, bB = bnd(Aset), bnd(Bset)
        if bA is not None and bB is not None and bA + bB >= c:
            return True
    return False


# ── logical redundancy vs record (§V) ─────────────────────────────────────────
def _entailed_prem(constraints, pr):
    cf = {v: Fraction(c) for v, c in pr["coeffs"].items()}
    rhs = Fraction(pr["rhs"]); rel = pr["rel"]
    if rel == ">=":
        st, v, _ = _lp(_cvec(cf), _prep(constraints)); return st == "opt" and v - float(rhs) >= -_LP_TOL
    if rel == "<=":
        st, v, _ = _lp(_cvec({k: -c for k, c in cf.items()}), _prep(constraints))
        return st == "opt" and v - float(-rhs) >= -_LP_TOL
    return (_entailed_prem(constraints, {"coeffs": pr["coeffs"], "rel": ">=", "rhs": pr["rhs"]})
            and _entailed_prem(constraints, {"coeffs": pr["coeffs"], "rel": "<=", "rhs": pr["rhs"]}))


def is_redundant_vs_records(pset, numeric, conclusion, records, exclude_skeleton=None):
    """A new conjecture is redundant if some existing record E — whose premises are
    implied by the new premises (properties ⊆ closure, numeric LP-entailed) — plus
    the Inventory derive the new conclusion with NO case split (linear + rounding)."""
    base = _premise_forms(numeric) + _unconditional_forms()
    base += _triggerable_conditionals(base)
    d0 = {v: int(c) for v, c in conclusion["coeffs"].items() if int(c) != 0}
    for E in records:
        if exclude_skeleton is not None and E.get("_skeleton") == exclude_skeleton:
            continue
        cj = E["conjecture"]
        eprops = [p["name"] for p in cj.get("properties_premises", [])]
        if not set(eprops).issubset(pset):
            continue
        enum = cj.get("numeric_premises", [])
        if not all(_entailed_prem(base, pr) for pr in enum):
            continue
        econcl = cj["conclusion"]
        extra = list(numeric) + [{"coeffs": {k: int(v) for k, v in econcl["coeffs"].items()},
                                  "rel": econcl["rel"], "rhs": int(econcl["rhs"])}]
        ctx = Context(premises=extra, depth=0, use_conditional_split=False, use_bnb=False,
                      use_lemmas=False, extra_directions=[d0, _neg(d0)])
        ctx.saturate()
        if _find_fact(ctx, conclusion) is not None:
            return True
    return False


# ── Dalmatian significance (§VI, IRIS binary significance) ────────────────────
DALMATIAN_FILTER = True
DALMATIAN_MIN_SUPPORT = 20


def _primary_bound(disp, primary, gvals):
    """From a primary-positive form ``a*primary + rest REL rhs``, the bound value on
    ``primary`` at a graph: ``(rhs - rest(g)) / a`` (rel '>=' → lower, '<=' → upper)."""
    coeffs = disp["coeffs"]
    a = Fraction(int(coeffs[primary]))
    rest = sum(Fraction(int(coeffs[v])) * gvals[v] for v in coeffs if v != primary)
    return disp["rel"], (Fraction(int(disp["rhs"])) - rest) / a


def dalmatian(props, numeric, conclusion, primary, existing, pool):
    if not pool_covered(props, numeric):
        return "unknown"
    support = dataset_subset(pool, props, numeric)
    if len(support) < DALMATIAN_MIN_SUPPORT:
        return "unknown"
    disp, prim = display_conclusion(conclusion, primary)
    comps = []
    for E in existing:
        cj = E["conjecture"]
        if E.get("primary_var") != prim:
            continue
        ed = {"coeffs": {k: int(v) for k, v in cj["conclusion"]["coeffs"].items()},
              "rel": cj["conclusion"]["rel"], "rhs": int(cj["conclusion"]["rhs"])}
        if int(ed["coeffs"].get(prim, 0)) <= 0 or ed["rel"] != disp["rel"]:
            continue
        comps.append((cj.get("properties_premises", []), cj.get("numeric_premises", []), ed))
    for g in support:
        gv = DED.vars_from_graph(g)
        gvals = {v: (gv[v] if gv[v] is not None else Fraction(0)) for v in VARS}
        _, new_val = _primary_bound(disp, prim, gvals)
        gp = INV.properties_of(g)
        best = None
        for eprops, enum, ed in comps:
            if not _graph_matches(g, gp, eprops, enum):
                continue
            _, ev = _primary_bound(ed, prim, gvals)
            best = ev if best is None else (max(best, ev) if disp["rel"] == ">=" else min(best, ev))
        if best is None:
            return "significant"
        if disp["rel"] == ">=" and new_val > best:
            return "significant"
        if disp["rel"] == "<=" and new_val < best:
            return "significant"
    return "not_significant"


# ── the per-premise-set pipeline ──────────────────────────────────────────────
_W_LEMMA_META = {}
_W_SNAPSHOT_RECORDS = []


def set_lemma_meta(m):
    global _W_LEMMA_META
    _W_LEMMA_META = m or {}


def set_snapshot_records(recs):
    global _W_SNAPSHOT_RECORDS
    _W_SNAPSHOT_RECORDS = recs or []


def process_premise_set(rng, pool, existing_hashes, stats, seed, accept="split_needed"):
    D.work_reset(GROUP_WORK_BUDGET)
    try:
        return _impl(rng, pool, existing_hashes, stats, seed, accept)
    except D.WorkBudgetExceeded:
        stats["too_slow"] += 1
        return None


def _main_var(coeffs):
    """Pick the display 'main variable': largest |coeff|, tie → VARS order."""
    best = None
    for v in VARS:
        c = abs(int(coeffs.get(v, 0)))
        if c == 0:
            continue
        if best is None or c > best[1]:
            best = (v, c)
    return best[0] if best else None


def _coeff1_var(coeffs):
    """§VII fallback primary: a remaining variable with coefficient 1 (then ±1,
    then largest |coeff|)."""
    for v in VARS:
        if int(coeffs.get(v, 0)) == 1:
            return v
    for v in VARS:
        if abs(int(coeffs.get(v, 0))) == 1:
            return v
    return _main_var(coeffs)


def _impl(rng, pool, existing_hashes, stats, seed, accept):
    _ctx_cache_clear()
    props, numeric = sample_premises(rng)
    props = dedup_properties(props)                 # §IV.1: drop implied property premises
    numeric = dedup_numeric(numeric)
    numeric = minimize_numeric_redundant(numeric)
    pset = property_closure({p["name"] for p in props})
    params = _prop_params(props)
    usable = finite_vars(pset)
    DED.set_active_inventory(pset, params)

    covered = pool_covered(props, numeric)
    if covered and not dataset_subset(pool, props, numeric):
        stats["empty_premises"] += 1
        return None

    primary = choose_primary(seed, usable)                      # §III rotation
    if primary is None:
        return None
    candidates = enumerate_candidates(numeric, usable, primary, stats, rng, accept)
    if not candidates:
        stats["no_candidate"] += 1
        return None
    rng.shuffle(candidates)

    for cand in candidates:
        # §VIII order (performance-adjusted, see note): linear → premise-minimise →
        # strengthen & drop terms (proof already over the minimized premises, so no
        # re-derivation is needed) → trivial/linear → decomposability (expensive, so
        # after the cheap filters) → skeleton → redundancy pre-check → counter-model.
        if linearly_derivable(numeric, cand):
            stats["linear_only"] += 1
            continue
        # premise minimisation first (cheap, cached) so the strengthened proof uses
        # exactly the minimized premises — avoids a separate re-proof step.
        pruned = minimize_premises_num(numeric, cand)
        pruned = minimize_numeric_redundant(pruned)
        res = strengthen_and_simplify(cand, pruned, primary)
        if res is None:
            stats["proof_reconstruct_failed"] += 1
            continue
        conclusion, ctx_m, fact = res
        ccoeffs = {v: int(c) for v, c in conclusion["coeffs"].items()}
        prim = primary if ccoeffs.get(primary, 0) != 0 else _coeff1_var(ccoeffs)
        if prim is None:
            continue
        n_terms = len([v for v in ccoeffs if v != prim and ccoeffs[v] != 0])
        if n_terms > MAX_CONCLUSION_TERMS:
            stats["too_many_terms"] += 1
            continue
        # trivial / linear (cheap)
        if _is_trivial(ccoeffs, int(conclusion["rhs"])):
            stats["trivial"] += 1
            continue
        if linearly_derivable(pruned, conclusion):
            stats["linear_only"] += 1
            continue
        # §IV decomposability filter (full deduction power)
        if is_decomposable(pruned, conclusion):
            stats["decomposable"] += 1
            continue
        skel = conjecture_skeleton(props, pruned, conclusion)
        # §V logical-redundancy pre-check against the run-start snapshot
        if is_redundant_vs_records(pset, pruned, conclusion, _W_SNAPSHOT_RECORDS):
            stats["redundant_vs_record"] += 1
            continue
        tb = traceback(ctx_m, fact)
        if _count_derivation_steps(tb) < 1:
            stats["too_shallow"] += 1
            continue
        ok, _msg = recheck(ctx_m, fact, pruned)
        if not ok:
            stats["recheck_failed"] += 1
            continue
        soundness_check(props, pruned, conclusion, pool)
        cm = counter_model(pruned, conclusion)
        if cm is not None:
            raise AssertionError(
                f"COUNTER-MODEL: not inventory-derivable.\n props={props}\n "
                f"numeric={pruned}\n conclusion={conclusion}\n model={cm}")
        # depth label
        depth_type = classify_depth(pruned, ccoeffs)
        if depth_type != accept:
            stats["depth_mismatch"] += 1
            continue
        # shortest proof
        proof_cost_initial = _pdiff(tb)
        tb, ctx_m, fact, proof_cost, shorten_rounds = shorten_proof(
            pruned, conclusion, tb, ctx_m, fact, proof_cost_initial)
        # lemma usage
        lemma_cnums = sorted(F._lemma_cnums_in(tb))
        if lemma_cnums:
            free = shortest_lemma_free(pruned, conclusion)
            if free is not None:
                ctx_m, fact, tb, proof_cost = free
                lemma_cnums = []
                stats["lemma_dropped_dependency"] += 1
        generation = (1 + max((_W_LEMMA_META[c]["generation"] for c in lemma_cnums), default=-1)) if lemma_cnums else 0
        proof_cost_expanded = proof_cost + sum(_W_LEMMA_META[c]["proof_cost_expanded"] for c in lemma_cnums)

        # attainment / IRIS on the real subset (if n ≤ 7 covered)
        feat_vars = iris_feature_vars(props, pruned, conclusion)
        if covered:
            subset = dataset_subset(pool, props, pruned)
            feats = [tuple(int(DED.vars_from_graph(g)[v]) for v in feat_vars) for g in subset]
            touch = sum(1 for f in feats
                        if sum(ccoeffs.get(v, 0) * f[i] for i, v in enumerate(feat_vars)) == int(conclusion["rhs"]))
            if touch == 0:
                stats["not_attained"] += 1
                continue
            attained = "yes"
            n_set = len(feats)
            dataset_size = n_set
            iris = _iris_from_feats(feats, feat_vars, ccoeffs, int(conclusion["rhs"]))
            touch_val = touch
        else:
            attained = "unknown"
            iris = {"T": 0.0, "R": 0.0, "L": 0.0, "score": 0.0}
            touch_val = None
            stats["skipped_pool_checks"] += 1

        sl = HARD.statement_length(pruned, conclusion)
        hard = (proof_cost_expanded / sl) if sl else 0.0
        h = conjecture_hash(props, pruned, conclusion)
        if h in existing_hashes:
            stats["duplicate"] += 1
            continue
        new_metrics = {"attained": attained, "touch": touch_val, "hardness": hard}
        all_inv = set()
        _used_inventory(tb, all_inv)
        inv_used = sorted(all_inv)
        renumber_steps(tb)
        proof_stats = _pstats(tb)
        disp, prim = display_conclusion(conclusion, prim)
        return {
            "seed": seed, "props": props, "numeric": pruned, "conclusion": conclusion,
            # aliases consumed by the generic run.py driver:
            "premises": {"props": props, "numeric": pruned, "primary": prim}, "disp": conclusion,
            "main_var": prim, "tb": tb, "inv_used": inv_used,
            "iris": {k: iris[k] for k in ("T", "R", "L", "score")},
            "attained": attained, "touch": touch_val, "hardness": hard,
            "depth_type": depth_type, "proof_stats": proof_stats,
            "proof_cost_initial": proof_cost_initial, "proof_cost": proof_cost,
            "proof_cost_expanded": proof_cost_expanded, "shorten_rounds": shorten_rounds,
            "generation": generation, "lemma_refs": [f"C{c}" for c in lemma_cnums],
            "hash": h, "skeleton": skel, "metrics": new_metrics,
            "properties": _prop_names(props),
            "conclusion_property": conclusion_property(props, disp),
            "dalmatian": "unknown",   # finalised in the main process at commit (§VI.4)
        }
    return None


def minimize_premises_num(premises, conclusion):
    kept = list(premises)
    i = 0
    while i < len(kept):
        trial = kept[:i] + kept[i + 1:]
        ctx = cached_context(trial)
        if _find_fact(ctx, conclusion) is not None:
            kept = trial
        else:
            i += 1
    return kept


def _iris_from_feats(feats, feat_vars, ccoeffs, rhs):
    if not feats:
        return {"T": 0.0, "R": 0.0, "L": 0.0, "score": 0.0}
    n = len(feats)
    touch = [f for f in feats
             if sum(ccoeffs.get(v, 0) * f[i] for i, v in enumerate(feat_vars)) == rhs]
    nt = len(touch)
    if nt == 0:
        return {"T": 0.0, "R": 0.0, "L": 0.0, "score": 0.0}
    T = nt / n
    arr = np.array(touch, dtype=float)
    R = float(np.linalg.matrix_rank(arr)) / nt if arr.size else 0.0
    data = np.array(feats, dtype=float)
    dd = IRIS._diameter(np.unique(data, axis=0))
    dt = IRIS._diameter(np.unique(arr, axis=0))
    L = 0.0 if dd == 0 else dt / dd
    return {"T": T, "R": R, "L": L, "score": T + R + L}


# ── main-process commit checks (§V re-check + §VI Dalmatian) ──────────────────
def main_commit_check(prop, committed, snapshot, pool):
    """Run at commit (main process, in index order).  ``committed`` is a list of
    ``{"skeleton", "data"}`` for records already written this run.  Returns
    ``(ok, reason)``; also finalises ``prop["dalmatian"]``."""
    pset = property_closure(set(prop["properties"]))
    # §V main re-check: redundancy vs this-run records (excluding a same-skeleton one)
    recs = [c["data"] for c in committed if c["skeleton"] != prop["skeleton"]]
    if is_redundant_vs_records(pset, prop["numeric"], prop["conclusion"], recs):
        return False, "redundant_vs_record_main"
    # §VI Dalmatian significance vs all existing (snapshot + this-run)
    existing = list(snapshot) + [c["data"] for c in committed]
    dj = dalmatian(prop["props"], prop["numeric"], prop["conclusion"], prop["main_var"],
                   existing, pool)
    prop["dalmatian"] = dj
    if DALMATIAN_FILTER and dj == "not_significant":
        return False, "not_significant"
    return True, None


# ── record assembly ───────────────────────────────────────────────────────────
def assemble_data(proposal, target, supersedes):
    props, numeric, conclusion = proposal["props"], proposal["numeric"], proposal["conclusion"]
    primary = proposal["main_var"]
    disp, prim = display_conclusion(conclusion, primary)
    return {
        "id": target,
        "created_at": datetime.now(timezone.utc).isoformat(),
        "generator": {"version": GENERATOR_VERSION, "seed": proposal["seed"]},
        "conjecture": {
            "formula": formula_string(props, numeric, conclusion, primary),
            "properties_premises": [{"name": p["name"], **({"param": p["param"]} if "param" in p else {})} for p in props],
            "numeric_premises": [{"text": pr.get("text", ""),
                                  "coeffs": {k: int(v) for k, v in pr["coeffs"].items()},
                                  "rel": pr["rel"], "rhs": int(pr["rhs"])} for pr in numeric],
            "conclusion": {"text": _render_isolated(disp, prim),
                           "coeffs": {k: int(v) for k, v in disp["coeffs"].items()},
                           "rel": disp["rel"], "rhs": int(disp["rhs"])},
            "natural_language": natural_language(props, numeric, conclusion, primary),
        },
        "primary_var": prim,
        "dalmatian": proposal.get("dalmatian", "unknown"),
        "properties": proposal["properties"],
        "conclusion_property": proposal["conclusion_property"],
        "proof": {"inventory_used": proposal["inv_used"], "lemmas_used": proposal["lemma_refs"],
                  "steps": proposal["tb"]},
        "iris": proposal["iris"],
        "attained": proposal["attained"], "touch": proposal["touch"],
        "depth_type": proposal["depth_type"], "proof_stats": proposal["proof_stats"],
        "proof_cost_initial": proposal["proof_cost_initial"], "proof_cost": proposal["proof_cost"],
        "proof_cost_expanded": proposal["proof_cost_expanded"], "shorten_rounds": proposal["shorten_rounds"],
        "generation": proposal["generation"], "supersedes": supersedes,
        "hardness": proposal["hardness"],
        "lean": {"theorem_name": target, "status": "compiled"},
    }


# ── pool / record loading ─────────────────────────────────────────────────────
def load_pool():
    # v1.1.2 §I.2: graphs are assumed nonempty — skip the 0-vertex graph on load
    # (the dataset file is kept intact).
    pool = [g for g in json.load(open(DATA))["graphs"] if g["n"] >= 1]
    return (pool, pool, pool)   # (objs, features-placeholder, obj_vars-placeholder)


def load_records(record_dir):
    """Parse all record JSONs (for the §V redundancy and §VI Dalmatian checks)."""
    out = []
    if not record_dir.exists():
        return out
    for d in sorted(record_dir.iterdir()):
        j = d / f"{d.name}.json"
        if j.exists():
            out.append(json.load(open(j)))
    return out


def load_existing_hashes(record_dir):
    hashes, max_id = {}, 0
    if not record_dir.exists():
        return hashes, max_id
    for d in record_dir.iterdir():
        j = d / f"{d.name}.json"
        if not j.exists():
            continue
        data = json.load(open(j))
        cj = data["conjecture"]
        props = [{"name": p["name"], **({"param": p["param"]} if "param" in p else {})}
                 for p in cj.get("properties_premises", [])]
        numeric = cj.get("numeric_premises", [])
        h = conjecture_hash(props, numeric, cj["conclusion"])
        hashes[h] = d.name
        try:
            max_id = max(max_id, int(d.name[1:]))
        except ValueError:
            pass
    return hashes, max_id


def build_skeleton_index(record_dir, features):
    idx = {}
    if not record_dir.exists():
        return idx
    for d in sorted(record_dir.iterdir()):
        j = d / f"{d.name}.json"
        if not j.exists():
            continue
        data = json.load(open(j))
        cj = data["conjecture"]
        props = [{"name": p["name"], **({"param": p["param"]} if "param" in p else {})}
                 for p in cj.get("properties_premises", [])]
        numeric = cj.get("numeric_premises", [])
        skel = conjecture_skeleton(props, numeric, cj["conclusion"])
        idx[skel] = {"name": d.name, "attained": data.get("attained", "yes"),
                     "touch": data.get("touch"), "hardness": data["hardness"],
                     "formula": cj["formula"], "supersedes": data.get("supersedes", [])}
    return idx


def select_lemma_library(record_dir):
    cand = []
    if record_dir.exists():
        for d in sorted(record_dir.iterdir()):
            j = d / f"{d.name}.json"
            if not j.exists():
                continue
            data = json.load(open(j))
            cj = data["conjecture"]
            if len(cj.get("numeric_premises", [])) > 2 or data.get("attained") != "yes":
                continue
            cand.append((int(d.name[1:]), data))
    cand.sort(key=lambda t: (len(t[1]["conjecture"].get("numeric_premises", [])),
                             -(t[1].get("touch") or 0), -t[1].get("hardness", 0.0), t[0]))
    cand = cand[:LEMMA_LIB_MAX]
    lemmas, lemma_meta, lemma_data = {}, {}, {}
    # v1.1 stage 1: lemma library mechanism present but conservatively empty
    # (graph lemmas as conditional theorems are introduced once the record grows).
    return lemmas, lemma_meta, lemma_data
