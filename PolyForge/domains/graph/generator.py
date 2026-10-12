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
from time import perf_counter
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

GENERATOR_VERSION = "1.3.1"
MAIN_COEFFS = (1, 2)          # main-variable coefficient
# v1.2 §III.5: other-term coefficients widened to |·| ≤ 3 so conclusions like
# 2m ≥ 3n (handshake under min_deg ≥ 3) can be expressed.
OTHER_COEFFS = (-3, -2, -1, 1, 2, 3)  # other-term coefficients
MAX_COEFF = 6                 # guard on display coefficients
MAX_CONCLUSION_TERMS = 3      # terms besides the main variable
# v1.2: products make far more directions bounded, so a premise set can yield
# ~1000 candidates.  Processing every one (each with the full filter stack) would
# blow the per-group work budget; cap how many are tried per set (the strongest
# per skeleton are kept first by enumerate_candidates' de-dup).
MAX_CANDIDATES_PER_SET = 40
GROUP_WORK_BUDGET = 120000
RO_MAX_RATIO = CG.RO_MAX_RATIO
MAX_SHORTEN_ROUNDS = 1
LEMMA_LIB_MAX = 50
POOL_N_MAX = 7                # dataset covers n ≤ 7
_LP_TOL = 1e-7

VARS = list(DED.VARS)
# v1.2: the LP/MILP works over ALL_VARS (invariants + product variables), so the
# product facts and McCormick envelopes (which mention P_n_mindeg / P_n_maxdeg /
# N2) have columns.  ``VARS`` stays the proposition variables used everywhere else.
_LP_VARS = list(DED.ALL_VARS)
_ALL_IDX = {v: i for i, v in enumerate(_LP_VARS)}
_NVARS = len(_LP_VARS)

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

# v1.2.2 §III: two-variable relational premises are allowed only between these
# naturally comparable variable pairs (finiteness still gates diam/radius/girth).
_REL_PAIRS = [frozenset(p) for p in (
    ("alpha", "tau"), ("omega", "chi"), ("omega", "alpha"), ("min_deg", "max_deg"),
    ("chi", "max_deg"), ("omega", "max_deg"), ("radius", "diam"), ("girth", "diam"),
    ("m", "n"), ("alpha", "n"), ("chi", "n"))]


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
        # v1.2.2 §III: two-variable relations (x≤y, x≥y, x≤2y, x≥2y) only between
        # naturally comparable variable pairs (the whitelist).
        avail = [tuple(sorted(p)) for p in _REL_PAIRS if set(p) <= set(uvars)]
        if not avail:
            return bound()
        x, y = rng.choice(avail)
        if rng.choice([True, False]):
            x, y = y, x
        rel = rng.choice([">=", "<="])
        mult = rng.choice([1, 2])
        rhs_txt = y if mult == 1 else f"{mult}*{y}"
        return {"coeffs": {x: 1, y: -mult}, "rel": rel, "rhs": 0,
                "text": f"{x} {rel} {rhs_txt}"}

    makers = [bound, bound, relation]
    # v1.2.1 §II: reject a numeric premise that is always true (Inventory-derivable
    # with no premises, e.g. alpha ≤ 2n since alpha ≤ n); resample it a few times.
    for _ in range(n_num):
        pr = None
        for _try in range(8):
            cand = rng.choice(makers)()
            goal = _as_ge_goal(cand)
            if goal is not None and _inventory_entails(goal):
                continue                            # always true — resample
            pr = cand
            break
        if pr is not None:
            numeric.append(pr)
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
    """Linear inventory facts only (NO product variables) — the basis for v_lin
    (§IV.1) and for the split tree's linear layer."""
    forms = []
    for e in DED.INVENTORY:
        forms.append(_conc_form(e["conclusion"]))
    return forms


def _product_forms():
    """Active product (handshake / edge-count) facts — §III."""
    return [_conc_form(e["conclusion"]) for e in DED.PRODUCT_FACTS]


def _active_product_vars():
    """Product variables carried by the active product facts (§III.1)."""
    act = set()
    for e in DED.PRODUCT_FACTS:
        for v in e["conclusion"]["coeffs"]:
            if v in DED.PRODUCT_VARS:
                act.add(v)
    return act


def _factor_bounds(linbase):
    """Integer bounds (a = ⌈min⌉, A = ⌊max⌋; None if unbounded/infeasible) of each
    product-factor variable over the LINEAR constraints ``linbase``.  These are the
    provable bounds the deducer rounds to, so the generated envelopes match."""
    mats = _prep(linbase)
    bnd = {}
    fvars = set()
    for (x, y) in DED.PRODUCT_VARS.values():
        fvars.add(x); fvars.add(y)
    for v in sorted(fvars):
        stlo, lo, _ = _lp(_cvec({v: 1}), mats)
        sthi, neg, _ = _lp(_cvec({v: -1}), mats)
        a = _ceil(lo - _LP_TOL) if stlo == "opt" else None
        A = -_ceil(neg - _LP_TOL) if sthi == "opt" else None   # max = −(min −v)
        bnd[v] = (a, A)
    return bnd


def _envelope_forms(linbase):
    """McCormick envelope constraints for the active products, from the integer
    factor bounds provable over ``linbase`` (§III.2).  Returns (coeffs,const,'>=')
    tuples — the same envelopes the deducer's product step emits."""
    active = _active_product_vars()
    if not active:
        return []
    bnd = _factor_bounds(linbase)
    forms = []
    for P, (x, y) in DED.PRODUCT_VARS.items():
        if P not in active:
            continue
        ax, Ax = bnd.get(x, (None, None))
        ay, Ay = bnd.get(y, (None, None))
        combos = []
        if ax is not None and ay is not None:
            combos.append((("lower", ax), ("lower", ay)))
        if Ax is not None and Ay is not None:
            combos.append((("upper", Ax), ("upper", Ay)))
        if ax is not None and Ay is not None:
            combos.append((("lower", ax), ("upper", Ay)))
        if Ax is not None and ay is not None:
            combos.append((("upper", Ax), ("lower", ay)))
        for (kx, bx), (ky, by_) in combos:
            coeffs, const = D.product_envelope_form(P, x, y, kx, bx, ky, by_)
            if P in coeffs:
                forms.append((coeffs, const, ">="))
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
        # v1.2.1 fix: honour the hypothesis relation.  _conc_form turns the
        # hypothesis into a ``hc·x + hk ≥ 0`` (or ``== 0``) form, so a "<=" cap
        # like the Turán ``omega ≤ r`` triggers when its MAX is within the cap —
        # the old code assumed a ">=" lower-bound hypothesis and silently failed
        # for the new "<=" conditionals.
        hc, hk, hrel = _conc_form(e["hypothesis"])
        st, v, _ = _lp(_cvec(hc), _prep(constraints))
        if st == "opt" and v + float(hk) >= -_LP_TOL:
            out.append(_conc_form(e["conclusion"]))
    return out


def _node_mats(linbase, products):
    """Build the LP matrices for a node: the linear constraints plus (if
    ``products``) the active product facts and the McCormick envelopes derived
    from this node's bounds (§III.2 / §III.4: envelopes regenerate per node)."""
    full = list(linbase)
    if products:
        full = full + _product_forms() + _envelope_forms(linbase)
    return _prep(full)


def _build_split_tree(prem_forms, assum_forms, depth, products=True):
    base = prem_forms + assum_forms + _unconditional_forms()
    linbase = base + _triggerable_conditionals(base)
    node = {"linbase": linbase, "mats": _node_mats(linbase, products),
            "products": products, "splits": []}
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
                ge = _build_split_tree(prem_forms, assum_forms + [(dict(expr), Fraction(-c), ">=")], depth - 1, products)
                le = _build_split_tree(prem_forms, assum_forms + [({v: -x for v, x in expr.items()}, Fraction(c - 1), ">=")], depth - 1, products)
                node["splits"].append((ge, le))
    return node


def _merge(rge, rle):
    if rge[0] == "unbounded" or rle[0] == "unbounded":
        return None
    feas = [r[1] for r in (rge, rle) if r[0] == "opt"]
    return min(feas) if feas else None


def _vint(node, cvec, depth, use_bnb=True):
    st, val, xstar = _lp(cvec, node["mats"])
    if st == "unbounded":
        return ("unbounded", None)
    if st != "opt":
        return ("infeasible", None)
    best = _ceil(val - _LP_TOL)
    if depth > 0:
        for ge, le in node["splits"]:
            rge = _vint(ge, cvec, depth - 1, use_bnb)
            rle = _vint(le, cvec, depth - 1, use_bnb)
            mv = _merge(rge, rle)
            if mv is not None and mv > best:
                best = mv
        pick = D._bnb_pick_var(xstar) if use_bnb else None
        if pick is not None:
            var, fl = pick
            # v1.2 §III.4: a B&B bound changes the factor bounds, so regenerate the
            # node (products + envelopes) from the tightened linear base.
            prod = node.get("products", True)
            lb_ge = node["linbase"] + [({var: Fraction(1)}, Fraction(-(fl + 1)), ">=")]
            lb_le = node["linbase"] + [({var: Fraction(-1)}, Fraction(fl), ">=")]
            ge = {"linbase": lb_ge, "mats": _node_mats(lb_ge, prod), "products": prod, "splits": []}
            le = {"linbase": lb_le, "mats": _node_mats(lb_le, prod), "products": prod, "splits": []}
            rge = _vint(ge, cvec, depth - 1, use_bnb)
            rle = _vint(le, cvec, depth - 1, use_bnb)
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


_NEG_INF = float("-inf")


def _accepts(accept, dtype):
    """§IV.5: product_needed and split_needed belong to the MAIN phase; the
    supplement phase takes only rounding_only."""
    if accept == "rounding_only":
        return dtype == "rounding_only"
    return dtype in ("split_needed", "product_needed")


def _classify(slin, vlin, s_np, v_np, s_p, v_p):
    """Decide the depth_type from the three bounds (linear / full-power-without-
    products / full-power-with-products).  Values are integer lifts; ``s_*`` are
    'opt'/'unbounded'/'infeasible'."""
    vnp = v_np if s_np == "opt" else _NEG_INF
    if vnp < v_p:                                   # products gave extra lift
        return "product_needed"
    if slin == "opt" and v_np == _ceil(vlin - _LP_TOL):
        return "rounding_only"                      # pure integer rounding
    return "split_needed"


def classify_depth(premises, direction):
    pf = _premise_forms(premises)
    lin = pf + _unconditional_forms()
    lin += _triggerable_conditionals(lin)
    cvec = _cvec({v: int(c) for v, c in direction.items()})
    slin, vlin, _ = _lp(cvec, _prep(lin))
    tree_np = _build_split_tree(pf, [], D.DEFAULT_SPLIT_DEPTH, products=False)
    tree_p = _build_split_tree(pf, [], D.DEFAULT_SPLIT_DEPTH, products=True)
    s_np, v_np = _vint(tree_np, cvec, D.DEFAULT_SPLIT_DEPTH)
    s_p, v_p = _vint(tree_p, cvec, D.DEFAULT_SPLIT_DEPTH)
    if s_p != "opt":
        return "split_needed"
    return _classify(slin, vlin, s_np, v_np, s_p, v_p)


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
    per-set seed), among the finiteness-valid variables, in fixed VARS order.
    v1.2.2 §I.6: tau is excluded — under the Gallai identity every tau-primary
    conclusion canonicalises to an alpha conclusion, so mining tau as primary only
    produces disguised duplicates."""
    uorder = [v for v in VARS if v in usable and v != "tau"]
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
    tree_np = _build_split_tree(pf, [], D.DEFAULT_SPLIT_DEPTH, products=False)
    tree_p = _build_split_tree(pf, [], D.DEFAULT_SPLIT_DEPTH, products=True)
    directions = enumerate_directions(usable, main)   # fixed deterministic order
    stats["directions_total"] += len(directions)
    out = []
    for order, d in enumerate(directions):
        cvec = _cvec(d)
        slin, vlin, _ = _lp(cvec, lin_mats)
        if slin == "infeasible":                    # premises have no model
            continue
        # screening uses the split tree WITHOUT B&B (cheap); B&B is applied in the
        # per-candidate classify_depth only (products already make most lifts here).
        s_p, v_p = _vint(tree_p, cvec, D.DEFAULT_SPLIT_DEPTH, use_bnb=False)
        if s_p != "opt":
            continue
        vlin_f = vlin if slin == "opt" else _NEG_INF
        if not (v_p > vlin_f + _LP_TOL):            # no lift beyond the linear bound
            stats["linear_only"] += 1
            continue
        s_np, v_np = _vint(tree_np, cvec, D.DEFAULT_SPLIT_DEPTH, use_bnb=False)
        dtype = _classify(slin, vlin, s_np, v_np, s_p, v_p)
        if not _accepts(accept, dtype):
            stats[dtype + "_skipped"] += 1
            continue
        # v1.2.1 §IV: rank by v_int − v_lin (∞ when the linear relaxation is
        # unbounded, i.e. a pure product/split lift), ties by enumeration order.
        margin = (v_p - vlin) if slin == "opt" else float("inf")
        out.append({"coeffs": dict(d), "rel": ">=", "rhs": int(v_p),
                    "margin": margin, "order": order})
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
        entry = {"coeffs": ic, "rel": ">=", "rhs": rhs,
                 "margin": cand["margin"], "order": cand["order"]}
        if key not in best or rhs > best[key]["rhs"]:
            best[key] = entry
    cands = list(best.values())
    cands.sort(key=lambda c: (-c["margin"], c["order"]))   # §IV deterministic order
    return cands


# ── logical-implication checks over the full engine (v1.2.1 §I / §III) ─────────
def _full_forms(premises):
    """Every fact form available to the engine under ``premises``: the premises,
    the linear inventory, triggerable conditionals, the product facts, and the
    McCormick envelopes derived from the premise bounds."""
    lin = _premise_forms(premises) + _unconditional_forms()
    lin = lin + _triggerable_conditionals(lin)
    return lin + _product_forms() + _envelope_forms(lin)


def _implies(antecedent, consequent):
    """Does ``antecedent`` + the UNIVERSAL Inventory (base facts, products,
    envelopes — holding for all graphs, with NO premises and NO property-conditional
    facts) logically entail ``consequent``?  Both are ``{coeffs, rel: '>=', rhs}``.

    Premises AND property-conditional facts are deliberately excluded: including the
    premises makes the check vacuous (the original is already provable), and
    including property facts (e.g. is_k_edge_connected ⟹ min_deg ≥ k) smuggles a
    premise consequence back in — which would wrongly let ``m ≥ 3`` "imply" ``m ≥
    n``.  The spec's own counterexample — m ≥ 6 ⇏ 2m ≥ 3n at n=100,m=10 — is a
    premise-free witness.  Rebuilds the base (no-property) inventory and restores
    the caller's afterwards.  Checked by LP: minimise the consequent LHS over the
    universal facts + the antecedent and test it stays ≥ the consequent rhs."""
    saved = (DED.INVENTORY, DED.PRODUCT_FACTS, DED.CONDITIONAL_THEOREMS, DED.INVENTORY_BY_NAME)
    DED.set_active_inventory(set(), {})
    try:
        base = _full_forms([])
        ac = {v: Fraction(c) for v, c in antecedent["coeffs"].items()}
        base = base + [(ac, Fraction(-antecedent["rhs"]), ">=")]
        st, v, _ = _lp(_cvec({v: int(c) for v, c in consequent["coeffs"].items()}), _prep(base))
        return st == "opt" and v - float(consequent["rhs"]) >= -_LP_TOL
    finally:
        DED.INVENTORY, DED.PRODUCT_FACTS, DED.CONDITIONAL_THEOREMS, DED.INVENTORY_BY_NAME = saved


def _inventory_entails(goal):
    """Is ``goal`` ({coeffs, rel: '>=', rhs}) provable from the Inventory ALONE
    (no premises), with full power (products, envelopes, rounding, case split)?
    Used to reject always-true premises.  Rebuilds the base (no-property) inventory
    and restores the caller's afterwards; uses the LP v_int (fast, full power)."""
    gc = {v: int(c) for v, c in goal["coeffs"].items() if int(c) != 0}
    if not gc:
        return Fraction(goal["rhs"]) <= 0
    global _BASE_TREE
    saved = (DED.INVENTORY, DED.PRODUCT_FACTS, DED.CONDITIONAL_THEOREMS, DED.INVENTORY_BY_NAME)
    DED.set_active_inventory(set(), {})
    try:
        if _BASE_TREE is None:
            _BASE_TREE = _build_split_tree([], [], D.DEFAULT_SPLIT_DEPTH, products=True)
        s, v = _vint(_BASE_TREE, _cvec(gc), D.DEFAULT_SPLIT_DEPTH, use_bnb=True)
        return s == "opt" and v >= int(goal["rhs"])
    finally:
        DED.INVENTORY, DED.PRODUCT_FACTS, DED.CONDITIONAL_THEOREMS, DED.INVENTORY_BY_NAME = saved


_BASE_TREE = None   # cached empty-premise (base-inventory) split tree for §II resampling


def _as_ge_goal(pr):
    """A premise/relation ``{coeffs, rel, rhs}`` as an equivalent ``>=`` goal, or
    None for equalities (handled as the conjunction of both directions elsewhere)."""
    if pr["rel"] == ">=":
        return {"coeffs": dict(pr["coeffs"]), "rel": ">=", "rhs": pr["rhs"]}
    if pr["rel"] == "<=":
        return {"coeffs": {v: -c for v, c in pr["coeffs"].items()}, "rel": ">=", "rhs": -pr["rhs"]}
    return None


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
            # v1.2.1 §III (v0.3 rule): a term may be dropped only when the reduced
            # conclusion is (a) provable — guaranteed by _strongest_in — AND (b) still
            # IMPLIES the current conclusion under the premises + Inventory + products
            # + envelopes.  (b) is a logical check, not "looks simpler": e.g. 2m ≥ 12
            # must NOT replace 2m ≥ 3n, since 2m ≥ 12 does not imply 2m ≥ 3n.
            if set(red_concl["coeffs"]) <= set(cur["coeffs"]) \
                    and _implies(red_concl, cur):
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
    """§III.6 / §VI.1 counter-model gate, relaxed for products.

    Search for an integer point satisfying premises + active inventory (linear AND
    product facts) + the McCormick envelopes + ¬conclusion.  Product variables are
    free integers in the relaxation (no ``P = x·y`` constraint — that is nonlinear).
    Returns ``None`` if infeasible (no counter-model), else ``(model, is_real)``
    where ``is_real`` is True iff the found point, taking the TRUE products
    ``x·y``, still satisfies everything and violates the conclusion (a genuine
    counter-model ⇒ a soundness bug, halt).  A point that only works in the relaxed
    sense (some ``P ≠ x·y``) is a ``relaxed_counter_model`` — reported, not fatal."""
    active_p = sorted(_active_product_vars())
    linbase = _premise_forms(premises) + _unconditional_forms()
    linbase = linbase + _triggerable_conditionals(linbase)
    env = _envelope_forms(linbase)
    prod_forms = _product_forms()
    ncond = len(DED.CONDITIONAL_THEOREMS)
    allvars = list(VARS) + active_p
    nv = len(allvars)
    n = nv + ncond
    idx = {v: i for i, v in enumerate(allvars)}
    bigM = 10 ** 7
    cons = []

    def row(d):
        r = [0.0] * n
        for k, v in d.items():
            r[idx[k]] += float(v)
        return r

    def add_form(coeffs, const, rel):                 # coeffs·x + const  rel  0
        rr = row(coeffs)
        if rel == "==":
            cons.append((rr, -float(const), -float(const)))
        else:                                         # >= 0
            cons.append(([-x for x in rr], None, float(const)))

    for e in DED.INVENTORY:
        co, k, rel = _conc_form(e["conclusion"])
        add_form(co, k, rel)
    for (co, k, rel) in prod_forms:                   # product facts (relaxed)
        add_form(co, k, rel)
    for (co, k, rel) in env:                          # envelopes (relaxed)
        add_form(co, k, rel)
    for bi, e in enumerate(DED.CONDITIONAL_THEOREMS):
        b = nv + bi
        hyp_rhs = float(e["hypothesis"]["rhs"])
        hyp_lhs = {v: Fraction(c) for v, c in e["hypothesis"]["coeffs"].items()}
        rr = row(hyp_lhs); rr[b] = bigM
        cons.append((rr, None, (hyp_rhs - 1) + bigM))
        cco, cck, crel = _conc_form(e["conclusion"])
        rr = row(cco); rr[b] = bigM
        cons.append((rr, -float(cck), None))
        if crel == "==":
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
    bu = np.array([1.0 if i >= nv else 10 ** 5 for i in range(n)])
    D.work_tick()
    try:
        res = milp(c=np.zeros(n), constraints=[LinearConstraint(A, lb, ub)],
                   integrality=np.ones(n), bounds=Bounds(bl, bu))
    except Exception:
        return None
    if not (res is not None and res.success and res.x is not None):
        return None
    model = {v: int(round(res.x[idx[v]])) for v in VARS}
    # exact values with the TRUE products substituted (this is what a real graph
    # point would satisfy); the relaxed P-values are ignored for the real check.
    tvals = dict(model)
    for P, (x, y) in DED.PRODUCT_VARS.items():
        tvals[P] = model[x] * model[y]

    def _sat(co, rel, r):
        lhs = sum(Fraction(c) * tvals[v] for v, c in co.items())
        r = Fraction(r)
        if rel in ("=", "=="):
            return lhs == r
        if rel == ">=":
            return lhs >= r
        return lhs <= r

    real = True
    for pr in premises:
        if not _sat(pr["coeffs"], pr["rel"], pr["rhs"]):
            real = False
    for e in DED.INVENTORY:
        c = e["conclusion"]
        if not _sat(c["coeffs"], c["rel"], c["rhs"]):
            real = False
    for e in DED.PRODUCT_FACTS:
        c = e["conclusion"]
        if not _sat(c["coeffs"], c["rel"], c["rhs"]):
            real = False
    for e in DED.CONDITIONAL_THEOREMS:
        hyp = e["hypothesis"]
        if _sat(hyp["coeffs"], hyp["rel"], hyp["rhs"]):
            c = e["conclusion"]
            if not _sat(c["coeffs"], c["rel"], c["rhs"]):
                real = False
    if _sat(conclusion["coeffs"], conclusion["rel"], conclusion["rhs"]):
        real = False                                  # conclusion actually holds here
    return (model, real)


# ── hashing / skeleton (§III.6) ───────────────────────────────────────────────
def _skel_lhs(coeffs):
    nz = {v: Fraction(c) for v, c in coeffs.items() if Fraction(c) != 0}
    prim = _prim(nz, Fraction(0))
    if prim is None:
        return ()
    return tuple(sorted((v, int(c)) for v, c in prim[0].items()))


# ── v1.2.2 §I: canonical forms modulo active identities ───────────────────────
def active_equalities(props, params):
    """Equality vectors ``(coeffs, const)`` meaning ``coeffs·v + const == 0`` valid
    under the property-closure of ``props``: Gallai α + τ − n = 0 (always); the
    tree identity m − n + 1 = 0; and the regular-degree identities 2m − d·n = 0,
    max_deg − d = 0, min_deg − d = 0."""
    pset = property_closure({p["name"] for p in props})
    eqs = [({"alpha": 1, "tau": 1, "n": -1}, 0)]
    d = params.get("is_regular")
    if "is_tree" in pset:
        eqs.append(({"m": 1, "n": -1}, 1))
    elif "is_regular" in pset and d is not None:
        eqs.append(({"m": 2, "n": -int(d)}, 0))
    if "is_regular" in pset and d is not None:
        eqs.append(({"max_deg": 1}, -int(d)))
        eqs.append(({"min_deg": 1}, -int(d)))
    return eqs


def _elim(coeffs, rhs, var, ecoeffs, econst):
    """Eliminate ``var`` in ``Σ coeffs·v ≥ rhs`` using ``ecoeffs·v + econst == 0``
    (``var`` pivot).  Returns the rewritten ``(coeffs, rhs)`` over Fractions."""
    a = Fraction(ecoeffs[var])
    cv = Fraction(coeffs.get(var, 0))
    if cv == 0:
        return {k: Fraction(c) for k, c in coeffs.items()}, Fraction(rhs)
    factor = cv / a                       # coeffs[var]·var = -factor·(rest + econst)
    out = {k: Fraction(c) for k, c in coeffs.items() if k != var}
    for w, sc in ecoeffs.items():
        if w == var:
            continue
        out[w] = out.get(w, Fraction(0)) - factor * Fraction(sc)
    out = {k: v for k, v in out.items() if v != 0}
    return out, Fraction(rhs) + factor * Fraction(econst)


def _to_ge_primitive(coeffs, rhs):
    """``Σ coeffs·v ≥ rhs`` → canonical ``{coeffs: coprime ints, rel: '>=', rhs: int}``
    (scaling by a positive rational preserves the ≥ direction)."""
    prim = _prim({k: Fraction(c) for k, c in coeffs.items()}, Fraction(-rhs))
    if prim is None:                      # all-zero LHS
        return {"coeffs": {}, "rel": ">=", "rhs": int(rhs) if Fraction(rhs).denominator == 1 else rhs}
    ic, nc = prim
    return {"coeffs": {v: int(x) for v, x in ic.items()}, "rel": ">=", "rhs": int(-nc)}


_CANON_PIVOT = [("tau", "alpha"), ("m", None), ("max_deg", None), ("min_deg", None)]


def canonical_conclusion(conclusion, props, params):
    """§I.2: substitute (in fixed order) τ→n−α, then m→n−1 or d·n/2, then
    max_deg,min_deg→d where the identity is active; reduce to a coprime-integer
    ``>=`` form.  Deterministic — used as the key for ALL filters (§I.3)."""
    eqs = {tuple(sorted(e[0].items())): e for e in active_equalities(props, params)}
    coeffs = {k: Fraction(c) for k, c in conclusion["coeffs"].items() if Fraction(c) != 0}
    rhs = Fraction(conclusion["rhs"])
    pset = property_closure({p["name"] for p in props})
    d = params.get("is_regular")
    coeffs, rhs = _elim(coeffs, rhs, "tau", {"alpha": 1, "tau": 1, "n": -1}, 0)
    if "is_tree" in pset:
        coeffs, rhs = _elim(coeffs, rhs, "m", {"m": 1, "n": -1}, 1)
    elif "is_regular" in pset and d is not None:
        coeffs, rhs = _elim(coeffs, rhs, "m", {"m": 2, "n": -int(d)}, 0)
    if "is_regular" in pset and d is not None:
        coeffs, rhs = _elim(coeffs, rhs, "max_deg", {"max_deg": 1}, -int(d))
        coeffs, rhs = _elim(coeffs, rhs, "min_deg", {"min_deg": 1}, -int(d))
    return _to_ge_primitive(coeffs, rhs)


def _equiv_forms(conclusion, eqs):
    """All ``>=`` forms reachable from ``conclusion`` by eliminating an EXISTING
    variable with each active identity at most once (used to find the shortest
    equivalent display form)."""
    results, seen = [], set()

    def key(c, r):
        prim = _prim(c, Fraction(-r))
        if prim is None:
            return None
        return (tuple(sorted((v, int(x)) for v, x in prim[0].items())),
                str(prim[1]))

    def rec(coeffs, rhs, used):
        k = key(coeffs, rhs)
        if k is None or k in seen:
            return
        seen.add(k)
        results.append((coeffs, rhs))
        for i, (ec, ek) in enumerate(eqs):
            if i in used:
                continue
            for p in ec:
                if Fraction(coeffs.get(p, 0)) != 0:
                    nc, nr = _elim(coeffs, rhs, p, ec, ek)
                    rec(nc, nr, used | {i})

    start = {k: Fraction(c) for k, c in conclusion["coeffs"].items() if Fraction(c) != 0}
    rec(start, Fraction(conclusion["rhs"]), frozenset())
    return results


def display_form(conclusion, props, params):
    """§I.4: among all equivalent rewrites (via the active identities), the one with
    the fewest terms; ties → the canonical form, then lexicographic."""
    eqs = active_equalities(props, params)
    canon = canonical_conclusion(conclusion, props, params)
    canon_key = tuple(sorted(canon["coeffs"].items()))
    best = None
    for (c, r) in _equiv_forms(conclusion, eqs):
        prim = _prim(c, Fraction(-r))
        if prim is None or prim[1].denominator != 1:
            continue
        ic = {v: int(x) for v, x in prim[0].items()}
        rr = int(-prim[1])
        if any(abs(x) > MAX_COEFF for x in ic.values()):
            continue
        items = tuple(sorted(ic.items()))
        cand = (len(ic), 0 if items == canon_key else 1, items, rr)
        if best is None or cand[:3] < best[:3]:
            best = cand
    if best is None:
        return canon
    return {"coeffs": dict(best[2]), "rel": ">=", "rhs": best[3]}


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


# ── v1.3.1 §III: decomposability with coefficient splitting ───────────────────
# Default per-candidate wall budget for the coefficient-split search.  The split
# space is tiny (≤4 conclusion variables ⇒ a handful of (shared-var, a+b, A|B)
# combinations), and each part's bound is cached, so 1.0 s is far more than any
# real candidate needs; it is only a guard against a pathological LP.  Timed-out
# candidates are conservatively kept (counted ``decomposition_timeout``).
DECOMP_SPLIT_TIME_BUDGET = 1.0
DECOMP_SPLIT_MAX_COEFF = 3


def _decomp_coeff_parts(L):
    """Yield ``(shared, a, b, partA, partB)``: ways to split one variable's
    coefficient ``L[shared] = a + b`` (``a``, ``b`` nonzero, |·| ≤ 3) and partition
    the OTHER variables into A, B so that each part has ≥ 1 variable and strictly
    fewer than |L| variables (so with one shared variable every part has ≥ 2 vars)."""
    vars_ = list(L)
    nvar = len(vars_)
    if nvar < 3:                                  # need each part < nvar and the shared in both
        return
    for v in vars_:
        others = [w for w in vars_ if w != v]
        no = len(others)
        for a in range(-DECOMP_SPLIT_MAX_COEFF, DECOMP_SPLIT_MAX_COEFF + 1):
            if a == 0:
                continue
            b = L[v] - a
            if b == 0 or abs(b) > DECOMP_SPLIT_MAX_COEFF:
                continue
            for mask in range(1, (1 << no) - 1):   # non-empty proper subsets → both groups non-empty
                gA = bin(mask).count("1")
                if gA > nvar - 2 or (no - gA) > nvar - 2:
                    continue                        # keep each part strictly below |L| variables
                groupA = [others[i] for i in range(no) if mask & (1 << i)]
                groupB = [others[i] for i in range(no) if not (mask & (1 << i))]
                partA = {v: a, **{w: L[w] for w in groupA}}
                partB = {v: b, **{w: L[w] for w in groupB}}
                yield (v, a, b, partA, partB)


def is_decomposable_coeff(premises, conclusion, time_budget=DECOMP_SPLIT_TIME_BUDGET):
    """v1.3.1 §III: is the conclusion ``L ≥ c`` decomposable when a single shared
    variable's coefficient is split across the two parts?  Returns
    ``(decomposable, info, timed_out)``.

    For each split, a cheap LP relaxation (with product envelopes) gives an upper
    estimate of each part's achievable bound; if the two estimates already sum
    below ``c`` the split cannot succeed and is pruned.  Surviving splits are bounded
    with full deduction power (the same engine used at generation); if the two full
    bounds sum to ≥ ``c`` the conclusion is decomposable.  Part bounds are cached."""
    L = {v: int(c) for v, c in conclusion["coeffs"].items() if int(c) != 0}
    c = int(conclusion["rhs"])
    if len(L) < 3:
        return False, None, False
    tree = _build_split_tree(_premise_forms(premises), [], D.DEFAULT_SPLIT_DEPTH, products=True)
    mats = tree["mats"]
    lp_cache, full_cache = {}, {}

    def _key(part):
        return tuple(sorted(part.items()))

    def lp_lo(part):
        k = _key(part)
        if k not in lp_cache:
            st, val, _ = _lp(_cvec(part), mats)
            lp_cache[k] = val if st == "opt" else None
        return lp_cache[k]

    def full_lo(part):
        k = _key(part)
        if k not in full_cache:
            st, val = _vint(tree, _cvec(part), D.DEFAULT_SPLIT_DEPTH)
            full_cache[k] = val if st == "opt" else None
        return full_cache[k]

    t0 = perf_counter()
    for (v, a, b, partA, partB) in _decomp_coeff_parts(L):
        if perf_counter() - t0 > time_budget:
            return False, None, True                     # timed out → conservatively keep
        la, lb = lp_lo(partA), lp_lo(partB)
        if la is None or lb is None:
            continue
        if la + lb < c - _LP_TOL:                         # §III.3 prune: can't reach c
            continue
        fa, fb = full_lo(partA), full_lo(partB)
        if fa is None or fb is None:
            continue
        if fa + fb >= c:
            return True, {"shared": v, "a": a, "b": b, "partA": dict(partA),
                          "partB": dict(partB), "bound_A": fa, "bound_B": fb}, False
    return False, None, False


# ── v1.3.1 §II: single-substantive-fact instances and family limiting ─────────
# Base facts are the elementary scaffolding the task excludes from "substantive"
# facts: variable non-negativity, n ≥ 1, chi/omega/alpha ≥ 1.  (Property→property
# implication rules live in the property closure, not the proof's inventory list.)
BASE_FACTS = ({f"nonneg_{v}" for v in DED.NONNEG_VARS}
              | {"n_ge_one", "chi_ge_one", "omega_ge_one", "alpha_ge_one"})


def substantive_facts(inv_used):
    """The substantive Inventory facts in a proof (all used facts minus base
    facts).  Product facts count; envelopes/rounding/case splits are not facts."""
    return sorted(set(inv_used) - BASE_FACTS)


def instance_of_fact(inv_used):
    """The single substantive fact a proof rests on, or ``None`` if it uses zero or
    more than one.  Such single-fact conjectures are parametric *instances*."""
    s = substantive_facts(inv_used)
    return s[0] if len(s) == 1 else None


def family_key(instance_of, props, numeric, canon):
    """v1.3.1 §II.3: the family key of an instance — its substantive fact, the
    premise skeleton (property names + constant-free premise shapes) and the
    canonical conclusion's variable set and direction (constants/coefficients of
    the conclusion ignored)."""
    prem = frozenset((p["name"],) for p in props)
    num = frozenset((_skel_lhs(pr["coeffs"]), pr["rel"], "*") for pr in numeric)
    cvars = frozenset(v for v, cc in canon["coeffs"].items() if int(cc) != 0)
    return ("FAM", instance_of, prem, num, (cvars, canon["rel"]))


def _record_family_key(data):
    """Family key of an existing record, or ``None`` if it is not an instance."""
    io = instance_of_fact(data.get("proof", {}).get("inventory_used", []))
    if io is None:
        return None
    props, numeric, canon = _record_props_canon(data)
    return family_key(io, props, numeric, canon)


def _record_metrics(data):
    return {"attained": data.get("attained", "yes"), "touch": data.get("touch"),
            "hardness": data.get("hardness", 0.0)}


def family_duplicate_vs(records, fam, new_metrics):
    """True if some record is a same-family instance that is NOT worse than the new
    one (so the new instance loses the family slot)."""
    for data in records:
        if _record_family_key(data) == fam and not skeleton_better(new_metrics, _record_metrics(data)):
            return True
    return False


# ── degenerate-premise filter (v1.2 §V) ───────────────────────────────────────
def premises_degenerate(premises):
    """True if the premises force the graph into a degenerate small regime — the
    engine (full power, incl. products) proves max_deg ≤ 1, m ≤ 1 or n ≤ 3.  Such
    premises only admit tiny/edgeless graphs, so the conjecture is discarded."""
    pf = _premise_forms(premises)
    tree = _build_split_tree(pf, [], D.DEFAULT_SPLIT_DEPTH, products=True)

    def upper(var):
        s, v = _vint(tree, _cvec({var: -1}), D.DEFAULT_SPLIT_DEPTH)
        return None if s != "opt" else -v            # upper bound = −(min of −var)

    for var, thr in (("max_deg", 1), ("m", 1), ("n", 3)):
        u = upper(var)
        if u is not None and u <= thr:
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

    # §V (v1.2) degenerate-premise filter: after premise minimisation, discard a
    # premise set that forces a degenerate small graph (max_deg ≤ 1, m ≤ 1, n ≤ 3).
    if premises_degenerate(numeric):
        stats["degenerate_premises"] += 1
        return None

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
    # §IV: candidates arrive sorted by (v_int − v_lin) desc, enumeration order; the
    # cap keeps the strongest; no shuffle (deterministic).
    if len(candidates) > MAX_CANDIDATES_PER_SET:
        stats["candidates_capped"] += len(candidates) - MAX_CANDIDATES_PER_SET
        stats["candidate_cap_sets"] += 1
        candidates = candidates[:MAX_CANDIDATES_PER_SET]

    for cand in candidates:
        # restore the FULL-premise active inventory for the linear-derivability gate
        # (per-candidate minimisation below re-points it at the pruned set).
        DED.set_active_inventory(pset, params)
        if linearly_derivable(numeric, cand):
            stats["linear_only"] += 1
            continue
        # v1.2.1 §I: minimise BOTH property and numeric premises (full power, with
        # the conclusion direction), then re-point the active inventory + ctx cache
        # at the pruned premise set for everything downstream.
        c_props, c_numeric = minimize_premises(props, numeric, cand, params)
        c_pset = property_closure({p["name"] for p in c_props})
        c_params = {p["name"]: p.get("param") for p in c_props if "param" in p}
        DED.set_active_inventory(c_pset, c_params)
        _ctx_cache_clear()                       # cache is invalid across inventories
        res = strengthen_and_simplify(cand, c_numeric, primary)
        if res is None:
            stats["proof_reconstruct_failed"] += 1
            continue
        conclusion, ctx_m, fact = res          # generation form (the proof proves this)
        ccoeffs = {v: int(c) for v, c in conclusion["coeffs"].items()}
        # v1.2.2 §I: the canonical form (modulo active identities) drives EVERY
        # filter; the display form is the shortest equivalent rewrite.
        canon = canonical_conclusion(conclusion, c_props, c_params)
        canon_coeffs = {v: int(c) for v, c in canon["coeffs"].items()}
        disp_internal = display_form(conclusion, c_props, c_params)
        disp_coeffs = {v: int(c) for v, c in disp_internal["coeffs"].items()}
        prim = primary if disp_coeffs.get(primary, 0) != 0 else _coeff1_var(disp_coeffs)
        if prim is None:
            continue
        n_terms = len([v for v in disp_coeffs if v != prim and disp_coeffs[v] != 0])
        if n_terms > MAX_CONCLUSION_TERMS:
            stats["too_many_terms"] += 1
            continue
        # trivial (on the canonical form) / linear (on the proven form)
        if _is_trivial(canon_coeffs, int(canon["rhs"])):
            stats["trivial"] += 1
            continue
        if linearly_derivable(c_numeric, conclusion):
            stats["linear_only"] += 1
            continue
        # §IV decomposability filter (full deduction power) — on the canonical form
        if is_decomposable(c_numeric, canon):
            stats["decomposable"] += 1
            continue
        # v1.3.1 §III: decomposability with a shared variable's coefficient split
        dec2, _dec_info, dec_timed = is_decomposable_coeff(c_numeric, canon)
        if dec_timed:
            stats["decomposition_timeout"] += 1
        if dec2:
            stats["decomposable_split"] += 1
            continue
        skel = conjecture_skeleton(c_props, c_numeric, canon)
        # §V logical-redundancy pre-check against the run-start snapshot (canonical)
        if is_redundant_vs_records(c_pset, c_numeric, canon, _W_SNAPSHOT_RECORDS):
            stats["redundant_vs_record"] += 1
            continue
        tb = traceback(ctx_m, fact)
        if _count_derivation_steps(tb) < 1:
            stats["too_shallow"] += 1
            continue
        ok, _msg = recheck(ctx_m, fact, c_numeric)
        if not ok:
            stats["recheck_failed"] += 1
            continue
        soundness_check(c_props, c_numeric, conclusion, pool)
        cm = counter_model(c_numeric, conclusion)
        if cm is not None:
            model, is_real = cm
            if is_real:
                raise AssertionError(
                    f"COUNTER-MODEL: not inventory-derivable.\n props={c_props}\n "
                    f"numeric={c_numeric}\n conclusion={conclusion}\n model={model}")
            # §VI.1: a relaxed-only model (some P ≠ x·y) is a statistic, not fatal.
            stats["relaxed_counter_model"] += 1
        # depth label (product_needed / split_needed / rounding_only)
        depth_type = classify_depth(c_numeric, ccoeffs)
        if not _accepts(accept, depth_type):
            stats["depth_mismatch"] += 1
            continue
        # shortest proof
        proof_cost_initial = _pdiff(tb)
        tb, ctx_m, fact, proof_cost, shorten_rounds = shorten_proof(
            c_numeric, conclusion, tb, ctx_m, fact, proof_cost_initial)
        # lemma usage
        lemma_cnums = sorted(F._lemma_cnums_in(tb))
        if lemma_cnums:
            free = shortest_lemma_free(c_numeric, conclusion)
            if free is not None:
                ctx_m, fact, tb, proof_cost = free
                lemma_cnums = []
                stats["lemma_dropped_dependency"] += 1
        generation = (1 + max((_W_LEMMA_META[c]["generation"] for c in lemma_cnums), default=-1)) if lemma_cnums else 0
        proof_cost_expanded = proof_cost + sum(_W_LEMMA_META[c]["proof_cost_expanded"] for c in lemma_cnums)

        # attainment / IRIS on the real subset (if n ≤ 7 covered)
        covered = pool_covered(c_props, c_numeric)
        feat_vars = iris_feature_vars(c_props, c_numeric, conclusion)
        if covered:
            subset = dataset_subset(pool, c_props, c_numeric)
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

        sl = HARD.statement_length(c_numeric, disp_internal)
        hard = (proof_cost_expanded / sl) if sl else 0.0
        h = conjecture_hash(c_props, c_numeric, canon)
        if h in existing_hashes:
            stats["duplicate"] += 1
            continue
        new_metrics = {"attained": attained, "touch": touch_val, "hardness": hard}
        all_inv = set()
        _used_inventory(tb, all_inv)
        inv_used = sorted(all_inv)
        renumber_steps(tb)
        proof_stats = _pstats(tb)
        # §VI.2: product conjectures are arithmetically sharp only in the relaxed
        # (envelope) sense — the counter-model gate cannot certify true optimality.
        arith_sharp = "relaxed" if proof_stats.get("product_steps", 0) > 0 else "exact"
        disp_oriented, _ = display_conclusion(disp_internal, prim)   # for property tag
        # v1.3.1 §II: instance detection (single substantive fact) + family limiting.
        # An instance uses the family key as its dedup skeleton, so the generic driver
        # keeps one representative per family (choosing the better via skeleton_better)
        # and replaces the loser; worse instances vs the run-start snapshot are dropped
        # here (worker pre-check), the main process re-checks vs this-run instances.
        instance_of = instance_of_fact(inv_used)
        if instance_of is not None:
            fam = family_key(instance_of, c_props, c_numeric, canon)
            if family_duplicate_vs(_W_SNAPSHOT_RECORDS, fam, new_metrics):
                stats["instance_family_duplicate"] += 1
                continue
            skel = fam
        return {
            "seed": seed, "props": c_props, "numeric": c_numeric, "conclusion": conclusion,
            "instance_of": instance_of,
            # aliases consumed by the generic run.py driver: ``disp`` is the internal
            # (>=) DISPLAY form (the formalizer/assembler orient it by ``primary``);
            # ``gen_conclusion`` is what the proof steps actually prove (pre-identity).
            "premises": {"props": c_props, "numeric": c_numeric, "primary": prim}, "disp": disp_internal,
            "gen_conclusion": conclusion, "canonical": canon,
            "main_var": prim, "tb": tb, "inv_used": inv_used,
            "iris": {k: iris[k] for k in ("T", "R", "L", "score")},
            "attained": attained, "touch": touch_val, "hardness": hard,
            "arith_sharp": arith_sharp,
            "depth_type": depth_type, "proof_stats": proof_stats,
            "proof_cost_initial": proof_cost_initial, "proof_cost": proof_cost,
            "proof_cost_expanded": proof_cost_expanded, "shorten_rounds": shorten_rounds,
            "generation": generation, "lemma_refs": [f"C{c}" for c in lemma_cnums],
            "hash": h, "skeleton": skel, "metrics": new_metrics,
            "properties": _prop_names(c_props),
            "conclusion_property": conclusion_property(c_props, disp_oriented),
            "dalmatian": "unknown",   # finalised in the main process at commit (§VI.4)
        }
    return None


def _provable_under(props, numeric, conclusion):
    """Is ``conclusion`` ({coeffs, rel: '>=', rhs}) provable under property premises
    ``props`` and numeric premises ``numeric`` with the FULL engine power used at
    generation (linear combination, rounding, case split, branch-and-bound,
    products + envelopes)?  Uses the same LP v_int as generation (fast); rebuilds
    the active inventory for ``props`` (caller restores it)."""
    pset = property_closure({p["name"] for p in props})
    pr = {p["name"]: p.get("param") for p in props if "param" in p}
    DED.set_active_inventory(pset, pr)
    d = {v: int(c) for v, c in conclusion["coeffs"].items() if int(c) != 0}
    if not d:
        return False
    tree = _build_split_tree(_premise_forms(numeric), [], D.DEFAULT_SPLIT_DEPTH, products=True)
    s, v = _vint(tree, _cvec(d), D.DEFAULT_SPLIT_DEPTH, use_bnb=True)
    return s == "opt" and v >= int(conclusion["rhs"])


def _finiteness_ok(props, conclusion, numeric):
    """True if every variable appearing in ``conclusion``/``numeric`` is still
    finite under the property closure of ``props`` (diam/radius need is_connected,
    girth needs has_cycle).  Guards premise drops against unsoundly exposing a ⊤."""
    used = set(conclusion["coeffs"])
    for pr in numeric:
        used |= set(pr["coeffs"])
    pset = property_closure({p["name"] for p in props})
    for v, need in DED.FINITENESS.items():
        if v in used and need not in pset:
            return False
    return True


def minimize_premises(props, numeric, conclusion, params):
    """v1.2.1 §I: remove every premise not needed to prove ``conclusion``.

    Greedily drop one premise at a time (numeric first, then property), re-proving
    with the SAME full power used to generate the conclusion (and the conclusion
    direction), until a fixpoint.  This subsumes: unused premises, premises implied
    by the rest (dropping them keeps the conclusion provable), and always-true
    premises (an Inventory-derivable premise adds nothing, so dropping it is safe).
    Property drops additionally respect the finiteness restrictions.  Returns the
    pruned ``(props, numeric)``; the active inventory is left set for the result."""
    props = [dict(p) for p in props]
    numeric = [dict(n) for n in numeric]
    changed = True
    while changed:
        changed = False
        for i in range(len(numeric)):
            trial = numeric[:i] + numeric[i + 1:]
            if _provable_under(props, trial, conclusion):
                numeric = trial
                changed = True
                break
        if changed:
            continue
        for i in range(len(props)):
            trial = props[:i] + props[i + 1:]
            if _finiteness_ok(trial, conclusion, numeric) \
                    and _provable_under(trial, numeric, conclusion):
                props = trial
                changed = True
                break
    # §I.3: re-run de-duplication (property closure, numeric redundancy) on the result
    props = dedup_properties(props)
    numeric = minimize_numeric_redundant(numeric)
    pset = property_closure({p["name"] for p in props})
    DED.set_active_inventory(pset, {p["name"]: p.get("param") for p in props if "param" in p})
    return props, numeric


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
    canon = prop.get("canonical", prop["conclusion"])
    # v1.3.1 §II: instance-family re-check vs snapshot + this-run instances.  A worse
    # same-family instance is dropped here; a better one passes and the generic driver
    # replaces the recorded representative (both share the family-key skeleton).
    io = prop.get("instance_of")
    if io is not None:
        fam = family_key(io, prop["props"], prop["numeric"], canon)
        existing = list(snapshot) + [c["data"] for c in committed]
        if family_duplicate_vs(existing, fam, prop["metrics"]):
            return False, "instance_family_duplicate"
    # §V main re-check: redundancy vs this-run records (excluding a same-skeleton one)
    recs = [c["data"] for c in committed if c["skeleton"] != prop["skeleton"]]
    if is_redundant_vs_records(pset, prop["numeric"], canon, recs):
        return False, "redundant_vs_record_main"
    # §VI Dalmatian significance vs all existing (snapshot + this-run); canonical form
    existing = list(snapshot) + [c["data"] for c in committed]
    dj = dalmatian(prop["props"], prop["numeric"], canon, prop["main_var"],
                   existing, pool)
    prop["dalmatian"] = dj
    if DALMATIAN_FILTER and dj == "not_significant":
        return False, "not_significant"
    return True, None


# ── v1.3 §I: displayed-form bridging step for md / json proof rendering ───────
# The proof steps derive the *generation* form; the recorded statement shows the
# *displayed* form.  When the two differ (an active Inventory identity rewrites the
# conclusion — Gallai α+τ=n, the tree identity, the regular-degree identities), the
# Lean proof closes the gap with one extra linear-combination step over the identity
# wrappers.  Prior to v1.3 that step was absent from the markdown proof and the JSON
# ``proof.steps`` (they ended at the generation form), so a reader saw "statement is
# A, proof derives B".  These helpers append the missing step so the rendered proof
# ends exactly at the displayed statement.  The reasoning/filtering pipeline is
# unchanged; this is purely a rendering fix.
RENDERED_WITH = "1.3"


def _max_fid(steps) -> int:
    m = 0
    for s in steps:
        m = max(m, int(s["fid"]))
        if s.get("rule") == "case_split":
            for cse in s["cases"]:
                m = max(m, _max_fid(cse["steps"]))
    return m


def _affine_key(coeffs, rel, rhs):
    """Normalise ``Σ coeffs·v REL rhs`` to a canonical (coprime, ``>=``-oriented)
    key so two inequalities are compared up to scaling and orientation."""
    c = {v: int(x) for v, x in coeffs.items() if int(x) != 0}
    rhs = int(rhs)
    if rel == "<=":
        c = {v: -x for v, x in c.items()}
        rhs = -rhs
        rel = ">="
    g = 0
    for x in c.values():
        g = gcd(g, abs(x))
    g = gcd(g, abs(rhs))
    if g > 1:
        c = {v: x // g for v, x in c.items()}
        rhs //= g
    return (tuple(sorted(c.items())), rel, rhs)


def _identities_for(props):
    """The active Inventory identities the Lean proof introduces when closing to
    the displayed form (Gallai always; tree / regular when premised)."""
    names = {p["name"] for p in props}
    ids = [("gallai", "the Gallai identity `alpha + tau = n`")]
    if "is_tree" in names:
        ids.append(("tree", "the tree identity `m = n - 1`"))
    if "is_regular" in names:
        ids.append(("regular",
                    "the regular-degree identities `2*m = d*n` and `max_deg = min_deg = d`"))
    return ids


def _bridging_step(proof_steps, disp_concl, props, disp_text):
    """Return the identity-rewrite step bridging the proven (generation) form to
    the displayed conclusion, or ``None`` if the two already coincide."""
    if not proof_steps:
        return None
    last = proof_steps[-1]
    if last.get("rule") == "identity_rewrite":       # already bridged — recompute afresh
        return None
    gen_rel = last.get("rel")
    if gen_rel == "==":
        return None
    gen_coeffs = {v: int(c) for v, c in last.get("coeffs", {}).items()}
    gen_rhs = -int(last.get("const", 0))
    gen_key = _affine_key(gen_coeffs, gen_rel, gen_rhs)
    disp_key = _affine_key(disp_concl["coeffs"], disp_concl["rel"], disp_concl["rhs"])
    if gen_key == disp_key:
        return None
    ids = _identities_for(props)
    human = "; ".join(h for _, h in ids)
    return {
        "fid": _max_fid(proof_steps) + 1,
        "rule": "identity_rewrite",
        "text": disp_text,
        "coeffs": {v: int(c) for v, c in disp_concl["coeffs"].items() if int(c) != 0},
        "rel": disp_concl["rel"],
        "rhs": int(disp_concl["rhs"]),
        "tactic": "linarith",
        "deps": [int(last["fid"])],
        "identities": [n for n, _ in ids],
        "identities_human": human,
        "note": f"Rewrite the proven form to the displayed conclusion using {human}.",
    }


def rerender_record(data):
    """v1.3 §I.3: re-render an existing record's markdown/JSON proof steps and
    natural-language statement to end at the displayed form, without touching the
    proposition or the Lean file.  Mutates and returns ``data``; sets
    ``rendered_with``.  Idempotent."""
    cj = data["conjecture"]
    props = cj.get("properties_premises", [])
    numeric = cj.get("numeric_premises", [])
    primary = data.get("primary_var")
    concl = cj["conclusion"]
    disp_concl = {"coeffs": {k: int(v) for k, v in concl["coeffs"].items()},
                  "rel": concl["rel"], "rhs": int(concl["rhs"])}
    # §I.2: keep natural_language consistent with the displayed form.
    cj["natural_language"] = natural_language(props, numeric, disp_concl, primary)
    # §I.1: append/refresh the displayed-form bridging step.
    apply_bridging(data["proof"]["steps"], disp_concl, props, concl["text"])
    data["rendered_with"] = RENDERED_WITH
    return data


def apply_bridging(steps, disp_concl, props, disp_text):
    """Mutate ``steps`` in place so the proof ends at the displayed form: drop any
    stale top-level bridging step, then append a fresh one when needed.  Idempotent."""
    while steps and steps[-1].get("rule") == "identity_rewrite":
        steps.pop()
    br = _bridging_step(steps, disp_concl, props, disp_text)
    if br is not None:
        steps.append(br)
    return steps


# ── record assembly ───────────────────────────────────────────────────────────
def assemble_data(proposal, target, supersedes):
    props, numeric = proposal["props"], proposal["numeric"]
    primary = proposal["main_var"]
    # v1.2.2: the displayed conclusion is the shortest equivalent (display) form;
    # ``canonical_form`` records the identity-canonical form used for de-duplication.
    disp_internal = proposal.get("disp", proposal["conclusion"])
    disp, prim = display_conclusion(disp_internal, primary)
    canon = proposal.get("canonical", disp_internal)
    canon_disp, canon_prim = display_conclusion(canon, None)
    disp_text = _render_isolated(disp, prim)
    # v1.3 §I: make the *recorded* proof end at the displayed conclusion.  The
    # bridging step is display-only (the Lean proof closes to the display form with
    # its own identity wrappers), so it must NOT be appended to ``proposal["tb"]``,
    # which the formalizer compiles — work on a shallow copy of the step list.
    steps = list(proposal["tb"])
    apply_bridging(steps, {"coeffs": disp["coeffs"], "rel": disp["rel"], "rhs": disp["rhs"]},
                   props, disp_text)
    return {
        "id": target,
        "created_at": datetime.now(timezone.utc).isoformat(),
        "generator": {"version": GENERATOR_VERSION, "seed": proposal["seed"]},
        "rendered_with": RENDERED_WITH,
        "conjecture": {
            "formula": formula_string(props, numeric, disp_internal, primary),
            "properties_premises": [{"name": p["name"], **({"param": p["param"]} if "param" in p else {})} for p in props],
            "numeric_premises": [{"text": pr.get("text", ""),
                                  "coeffs": {k: int(v) for k, v in pr["coeffs"].items()},
                                  "rel": pr["rel"], "rhs": int(pr["rhs"])} for pr in numeric],
            "conclusion": {"text": _render_isolated(disp, prim),
                           "coeffs": {k: int(v) for k, v in disp["coeffs"].items()},
                           "rel": disp["rel"], "rhs": int(disp["rhs"])},
            "canonical_form": {"text": _render_isolated(canon_disp, canon_prim),
                               "coeffs": {k: int(v) for k, v in canon_disp["coeffs"].items()},
                               "rel": canon_disp["rel"], "rhs": int(canon_disp["rhs"])},
            "natural_language": natural_language(props, numeric, disp_internal, primary),
        },
        "primary_var": prim,
        "dalmatian": proposal.get("dalmatian", "unknown"),
        "properties": proposal["properties"],
        "conclusion_property": proposal["conclusion_property"],
        "instance_of": proposal.get("instance_of"),
        "proof": {"inventory_used": proposal["inv_used"], "lemmas_used": proposal["lemma_refs"],
                  "steps": steps},
        "iris": proposal["iris"],
        "attained": proposal["attained"], "touch": proposal["touch"],
        "arith_sharp": proposal.get("arith_sharp", "exact"),
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


def _record_props_canon(data):
    """A record's (props, numeric, canonical-conclusion) for de-dup / skeleton keys
    (v1.2.2 §I.3).  Uses the stored ``canonical_form`` if present, else canonicalises
    the display conclusion on the fly."""
    cj = data["conjecture"]
    props = [{"name": p["name"], **({"param": p["param"]} if "param" in p else {})}
             for p in cj.get("properties_premises", [])]
    numeric = cj.get("numeric_premises", [])
    params = {p["name"]: p.get("param") for p in props if "param" in p}
    c = cj.get("canonical_form") or cj["conclusion"]
    coeffs = {k: int(v) for k, v in c["coeffs"].items()}
    rhs = int(c["rhs"])
    if c["rel"] == "<=":                         # convert display orientation to internal >=
        coeffs = {k: -v for k, v in coeffs.items()}; rhs = -rhs
    canon = canonical_conclusion({"coeffs": coeffs, "rel": ">=", "rhs": rhs}, props, params)
    return props, numeric, canon


def load_existing_hashes(record_dir):
    hashes, max_id = {}, 0
    if not record_dir.exists():
        return hashes, max_id
    for d in record_dir.iterdir():
        j = d / f"{d.name}.json"
        if not j.exists():
            continue
        data = json.load(open(j))
        props, numeric, canon = _record_props_canon(data)
        h = conjecture_hash(props, numeric, canon)
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
        props, numeric, canon = _record_props_canon(data)
        # v1.3.1 §II: instances dedup by family key (so a new better instance of the
        # same family supersedes the recorded one via the generic skeleton machinery).
        io = instance_of_fact(data.get("proof", {}).get("inventory_used", []))
        skel = family_key(io, props, numeric, canon) if io else conjecture_skeleton(props, numeric, canon)
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
