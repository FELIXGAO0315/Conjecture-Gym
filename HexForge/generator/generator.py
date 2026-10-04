"""Conjecture generator: sample premises, deduce, select, formalise, score, write.

Exposes functions only (no CLI); ``run.py`` drives them.  A single deduction
closure yields many candidate p₆ facts, which are filtered, de-duplicated,
minimised by traceback, exactly re-checked, regression-tested on every real
p-vector, formalised in Lean, scored, and written to ``record/C{n}/``.
"""

from __future__ import annotations

import json
import os
import random
import shutil
from collections import defaultdict
from datetime import datetime, timezone
from fractions import Fraction
from math import gcd
from pathlib import Path

import numpy as np
from scipy.optimize import linprog, milp, LinearConstraint, Bounds

from ..anvil import deducer as D
from ..anvil.deducer import Context, traceback, recheck, fact_text, vars_from_pvec
from ..anvil import inventory as INV
from ..anvil.inventory import PROP_VARS, ALL_VARS
from ..formalizer import formalizer as F
from ..scoring import iris as IRIS
from ..scoring import hardness as HARD

ROOT = Path(__file__).resolve().parent.parent           # HexForge/
DATA = ROOT / "data" / "plantri_pool.json"
RECORD = ROOT / "record"

GENERATOR_VERSION = "0.7"
MAX_COEFF = 6

# v0.6.5 §2: the old wall-clock DIRECTION_BUDGET_SEC (truncate enumeration after N
# seconds, keeping a random subset) is removed — it made the candidate set depend on
# machine speed.  All directions are now enumerated; runaway groups are cut by the
# deterministic GROUP_WORK_BUDGET below.

# v0.6.4 §IV: rounding_only conjectures are the easy tier.  Generation now runs in
# two phases (see run.py): a MAIN phase that produces only ``split_needed`` and a
# SUPPLEMENT phase that produces only ``rounding_only``.  Each worker is told which
# depth_type to ``accept``; a direction of the other type is dropped immediately
# after enumeration (no proof reconstruction), exactly as v0.6.3 dropped
# rounding_only via REQUIRE_SPLIT.
#
# v0.6.7 §3: the supplement phase writes AT MOST ``floor(S * RO_MAX_RATIO)``
# rounding_only records (an upper cap, not a fixed target), where S is the number of
# split_needed records from the main phase (so rounding_only are at most 20% of the
# total).  Whatever the supplement phase manages within its time/conditions is kept;
# it is not required to fill the cap.
RO_MAX_RATIO = 0.25

# v0.6.7 §1: cost-bounded re-proving — after the engine finds a proof, re-prove the
# same conclusion under cheaper method restrictions and keep the lowest-cost proof,
# at most this many compression rounds.
MAX_SHORTEN_ROUNDS = 1

# v0.7 §1: lemma library size cap.  From the record, the conjectures with <= 2
# premises and attained == "yes" become reusable conditional theorems; if more than
# this many qualify, the deterministic ordering in ``select_lemma_library`` trims it.
LEMMA_LIB_MAX = 50

# v0.6.5 §2: deterministic per-group work budget — the max number of LP/MILP solves
# a single premise set may trigger (counted across the deducer + generator via
# deducer.work_tick) before the whole group is discarded (``too_slow``).  This
# replaces the old wall-clock DIRECTION_BUDGET_SEC, which broke reproducibility.
# Recalibrated for v0.6.6 (branch-and-bound makes groups heavier): 5-min depth-3+B&B
# probe, seed 2024, 232 groups — per-group solve count p50=1395, p90=16039, p95=56803;
# PRODUCTIVE groups top out at 112428 solves, while UNPRODUCTIVE groups run to the
# probe cap (200k).  120000 keeps every productive group observed and cuts only the
# unproductive long tail (8 groups >120k, all unproductive), per §3.
GROUP_WORK_BUDGET = 120000

# v0.6.3 §3: at most this many terms besides p_6 in a conclusion (the merged
# big_faces expression sum_pk_after_p6 counts as a single term).
MAX_CONCLUSION_TERMS = 3

# v0.2 §3: require the (strengthened) conclusion to be attained with equality by
# at least one real polytope (IRIS T > 0).  Switchable to mark-only later.
REQUIRE_ATTAINED = True

# v0.4 §1: keep only lower bounds on p_6 (Inventory only bounds p_6 from below;
# upper bounds would carry no deductive content beyond a premise f_2 <= c).
ALLOW_UPPER_BOUNDS = False

# v0.4 §3: plantri_pool.json only covers f_2 <= POOL_F2_MAX.  A premise f_2 >= c
# with c > POOL_F2_MAX has no witness in the pool, so pool-based checks (non-empty
# and attainment) are skipped and correctness rests on the deducer + Lean.
POOL_F2_MAX = 28

# face_split vector:  f_2 - (p_3 + ... + p_10 + sum_pk_after_p10) = 0
_FACE_VARS = [v for v in PROP_VARS if v not in ("f_2",)]
_FACE = dict({"f_2": 1}, **{v: -1 for v in _FACE_VARS})

# v0.6.2 §1: big_faces = Σ_{k≥7} p_k (= p_7+..+p_{M_MAX}+tail; at M_MAX=6 it is
# exactly the single tail variable).  A fixed linear expression, not a variable.
BIG_FACES = {v: 1 for v in INV.TAIL_COUNT_VARS}
TAIL = INV.TAIL_VAR

# The three Inventory *theorems* counted as "inventory" (everything else in the
# axiom base is a HexLemmas lemma or a non-negativity fact).
INVENTORY_THEOREMS = {"Juc_EulerFormula", "JucovicTheorem", "Barnette_P6Bound"}

_LP_TOL = 1e-7

# pretty names -----------------------------------------------------------------
PRETTY = {v: v for v in PROP_VARS}
PRETTY["sum_pk_after_p6"] = "sum_pk_after_p6"   # merged big_faces display name

# v0.6.2 §1.2: display order including the merged big_faces expression.
_do = (["p_3", "p_4", "p_5", "p_6"] + [f"p_{k}" for k in range(7, INV.M_MAX + 1)]
       + [TAIL])
if "sum_pk_after_p6" not in _do:
    _do.append("sum_pk_after_p6")
DISPLAY_ORDER = _do + ["f_2"]


def _merge_tail_display(coeffs: dict) -> dict:
    """§1.2: for DISPLAY only — if p_7..p_10 and sum_pk_after_p10 all carry the
    same nonzero coefficient, present them as the single expression
    ``sum_pk_after_p6`` (= Σ_{k>=7} p_k).  The canonical form used for the
    skeleton / scoring is unchanged."""
    tc = list(INV.TAIL_COUNT_VARS)
    vals = set(int(coeffs.get(v, 0)) for v in tc)
    base = {k: int(c) for k, c in coeffs.items() if k not in tc}
    if len(vals) == 1 and next(iter(vals)) != 0:
        base["sum_pk_after_p6"] = next(iter(vals))
    else:
        for v in tc:
            if int(coeffs.get(v, 0)) != 0:
                base[v] = int(coeffs[v])
    return base


# ── pool loading ─────────────────────────────────────────────────────────────
def load_pool():
    """Return ``(pvecs, features)`` where ``pvecs`` is the list of face-count
    dicts and ``features`` the list of IRIS feature 6-tuples."""
    with open(DATA) as fh:
        raw = json.load(fh)
    pvecs = [entry["p_vec"] for entry in raw["p_vecs"]]
    features = [IRIS.features_from_pvec(pv) for pv in pvecs]
    return pvecs, features


# ── premise sampling ─────────────────────────────────────────────────────────
def sample_premises(rng: random.Random) -> list:
    """Sample 1–3 premises from the allowed forms."""
    n = rng.randint(1, 3)
    templates = []

    # v0.6.1: premises may mention p_3,p_4,p_5 and the large faces p_7..p_10 and
    # the tail — never p_6 (the target).
    SMALLV = ["p_3", "p_4", "p_5"] + [f"p_{k}" for k in range(7, INV.M_MAX + 1)]

    def small_var():
        return rng.choice(SMALLV)

    def add_small_eq0():
        v = small_var()
        return {"coeffs": {v: 1}, "rel": "=", "rhs": 0, "text": f"{v} = 0"}

    def add_small_le():
        v = small_var()
        c = rng.randint(1, 4)
        return {"coeffs": {v: 1}, "rel": "<=", "rhs": c, "text": f"{v} <= {c}"}

    def add_small_ge():
        v = small_var()
        c = rng.randint(1, 3)
        return {"coeffs": {v: 1}, "rel": ">=", "rhs": c, "text": f"{v} >= {c}"}

    def add_tail():
        c = rng.randint(1, 5)
        rel = rng.choice([">=", "<="])
        return {"coeffs": {TAIL: 1}, "rel": rel, "rhs": c,
                "text": f"{TAIL} {rel} {c}"}

    def add_f2():
        c = rng.randint(7, 60)
        rel = rng.choice([">=", "<="])
        return {"coeffs": {"f_2": 1}, "rel": rel, "rhs": c, "text": f"f_2 {rel} {c}"}

    def add_big_faces():
        # v0.6.2 §1: big_faces = p_7 + ... + p_10 + sum_pk_after_p10 as a single
        # premise expression (c in 0..6); helps trigger Barnette.
        c = rng.randint(0, 6)
        rel = rng.choice([">=", "<="])
        return {"coeffs": dict(BIG_FACES), "rel": rel, "rhs": c,
                "text": f"big_faces {rel} {c}"}

    def add_relation():
        x, y = rng.sample(SMALLV, 2)
        a, b = rng.randint(1, 3), rng.randint(1, 3)
        return {"coeffs": {x: a, y: -b}, "rel": ">=", "rhs": 0,
                "text": f"{a}*{x} >= {b}*{y}"}

    makers = [add_small_eq0, add_small_le, add_small_ge, add_tail, add_f2,
              add_big_faces, add_relation]
    # bias towards including f_2 >= 7 (activates Jučovič) roughly half the time
    prem = []
    if rng.random() < 0.55:
        c = rng.randint(7, 60)
        prem.append({"coeffs": {"f_2": 1}, "rel": ">=", "rhs": c,
                     "text": f"f_2 >= {c}"})
    while len(prem) < n:
        prem.append(rng.choice(makers)())
    # deduplicate identical premises (by variable-support + rel)
    seen = set()
    out = []
    for pr in prem:
        key = (tuple(sorted(pr["coeffs"].items())), pr["rel"], pr["rhs"])
        if key not in seen:
            seen.add(key)
            out.append(pr)
    return out


def _pvec_satisfies(vals: dict, premises: list) -> bool:
    for pr in premises:
        lhs = sum(Fraction(c) * vals.get(v, 0) for v, c in pr["coeffs"].items())
        rhs = Fraction(pr["rhs"])
        if pr["rel"] == "=" and lhs != rhs:
            return False
        if pr["rel"] == ">=" and lhs < rhs:
            return False
        if pr["rel"] == "<=" and lhs > rhs:
            return False
    return True


def premises_nonempty(premises: list, pvec_vars: list) -> bool:
    return any(_pvec_satisfies(v, premises) for v in pvec_vars)


def pool_covered(premises: list) -> bool:
    """False iff some premise ``f_2 >= c`` has c > POOL_F2_MAX (no pool witness
    possible), in which case pool-based checks are skipped (§3)."""
    for pr in premises:
        supp = [v for v, c in pr["coeffs"].items() if c]
        if supp == ["f_2"] and pr["rel"] == ">=" and \
                Fraction(pr["rhs"]) / Fraction(pr["coeffs"]["f_2"]) > POOL_F2_MAX:
            return False
    return True


# ── deduction cache (§4) ─────────────────────────────────────────────────────
# Memoise saturated contexts by (premises, extra_directions).  The algorithm's
# sequence of calls is unchanged; identical calls return the identical pool, so
# results (conclusions, proofs, scores) are unaffected — only recomputation is
# avoided.  Fids are renumbered deterministically at record-build time, so output
# is independent of how many contexts were actually built.
_CTX_CACHE: dict = {}
_CTX_ORDER: list = []
_CTX_CAP = 256
# Toggle for the performance-equivalence check (HEXFORGE_NOCACHE=1 disables the
# cache; output must be identical with and without it).
USE_CACHE = os.environ.get("HEXFORGE_NOCACHE") != "1"


def _ctx_cache_clear():
    _CTX_CACHE.clear()
    _CTX_ORDER.clear()


def _dir_sig(extra_dirs):
    return tuple(sorted(tuple(sorted((v, int(c)) for v, c in d.items()))
                        for d in (extra_dirs or [])))


def _prem_sig(premises):
    return tuple(sorted((tuple(sorted(pr["coeffs"].items())), pr["rel"],
                         int(pr["rhs"])) for pr in premises))


def cached_context(premises, extra_directions=None, use_lemmas=True):
    if not USE_CACHE:
        ctx = Context(premises=premises, depth=D.DEFAULT_SPLIT_DEPTH,
                      extra_directions=extra_directions, use_lemmas=use_lemmas)
        ctx.saturate()
        return ctx
    key = (_prem_sig(premises), _dir_sig(extra_directions), use_lemmas)
    ctx = _CTX_CACHE.get(key)
    if ctx is not None:
        return ctx
    ctx = Context(premises=premises, depth=D.DEFAULT_SPLIT_DEPTH,
                  extra_directions=extra_directions, use_lemmas=use_lemmas)
    ctx.saturate()
    _CTX_CACHE[key] = ctx
    _CTX_ORDER.append(key)
    if len(_CTX_ORDER) > _CTX_CAP:
        old = _CTX_ORDER.pop(0)
        _CTX_CACHE.pop(old, None)
    return ctx


# ── deterministic fid renumbering (§4) ───────────────────────────────────────
def renumber_steps(tb: list) -> list:
    """Renumber every step's fid (and dep references) to 1,2,3,… in traversal
    order, so the recorded proof is independent of the global fact counter."""
    mapping: dict = {}
    counter = [0]

    def first(steps):
        for s in steps:
            counter[0] += 1
            mapping[s["fid"]] = counter[0]
            if s["rule"] == "case_split":
                for cse in s["cases"]:
                    first(cse["steps"])

    def rewrite(steps):
        for s in steps:
            s["fid"] = mapping[s["fid"]]
            if "deps" in s:
                s["deps"] = [mapping[d] for d in s["deps"]]
            if s["rule"] == "case_split":
                for cse in s["cases"]:
                    rewrite(cse["steps"])

    first(tb)
    rewrite(tb)
    return tb


# ── candidate selection ──────────────────────────────────────────────────────
def _primitive_int(coeffs: dict, const: Fraction):
    prim = D._primitive(coeffs, const)
    if prim is None:
        return None
    ic, nc = prim
    return {v: int(c) for v, c in ic.items()}, nc


def _count_derivation_steps(tb: list) -> int:
    n = 0
    for s in tb:
        if s["rule"] in ("combination", "rounding", "conditional", "case_split"):
            n += 1
        if s["rule"] == "case_split":
            for c in s["cases"]:
                n += _count_derivation_steps(c["steps"])
    return n


def _used_inventory(tb: list, acc: set):
    for s in tb:
        if s.get("inventory"):
            acc.add(s["inventory"])
        if s["rule"] == "case_split":
            for c in s["cases"]:
                _used_inventory(c["steps"], acc)


def _used_premise_texts(tb: list, acc: set):
    for s in tb:
        if s["rule"] == "premise":
            acc.add(s["text"])
        if s["rule"] == "case_split":
            for c in s["cases"]:
                _used_premise_texts(c["steps"], acc)


# ── canonical form (§2): eliminate f_2 via face_split ────────────────────────
# face_split:  f_2 = p_3 + p_4 + p_5 + p_6 + sum_pk_after_p6
_FACE_SPLIT_SUB = [v for v in PROP_VARS if v != "f_2"]   # p_3..p_10, tail


def canonicalize(coeffs: dict) -> dict:
    """Replace f_2 by p_3+p_4+p_5+p_6+sum_pk_after_p6, giving a form over the
    five remaining proposition variables (plus p_6)."""
    out = {v: Fraction(c) for v, c in coeffs.items() if v != "f_2"}
    a = Fraction(coeffs.get("f_2", 0))
    if a != 0:
        for v in _FACE_SPLIT_SUB:
            out[v] = out.get(v, Fraction(0)) + a
    return {v: c for v, c in out.items() if c != 0}


# ── minimal equivalent form (§1) ─────────────────────────────────────────────
def minimal_form(coeffs: dict) -> dict:
    """Among all forms equivalent under face_split (adding integer multiples of
    ``f_2 − p_3 − p_4 − p_5 − p_6 − sum_pk_after_p6``), return the one with the
    fewest non-zero terms (ties: prefer p_6 present, then smallest coefficients).
    The right-hand side is unaffected (face_split has rhs 0)."""
    base = {v: Fraction(c) for v, c in coeffs.items() if Fraction(c) != 0}
    cand_t = {Fraction(0)}
    for v, fv in _FACE.items():
        cand_t.add(-base.get(v, Fraction(0)) / fv)
    best = None
    for t in cand_t:
        if t.denominator != 1:
            continue
        nc = {}
        for v, fv in _FACE.items():
            c = base.get(v, Fraction(0)) + t * fv
            if c != 0:
                nc[v] = c
        score = (len(nc), 0 if nc.get("p_6", 0) != 0 else 1,
                 max((abs(c) for c in nc.values()), default=Fraction(0)))
        if best is None or score < best[0]:
            best = (score, nc)
    return best[1]


def minimal_has_p6(coeffs: dict) -> bool:
    return minimal_form(coeffs).get("p_6", 0) != 0


# ── p_6-isolated display form (§4) ───────────────────────────────────────────
def display_conclusion(min_coeffs: dict, rhs: int) -> dict:
    """Orient the minimal form so p_6 is alone on the left with a positive,
    coprime coefficient: ``a·p_6 >= rest`` or ``a·p_6 <= rest``."""
    a = Fraction(min_coeffs.get("p_6", 0))
    if a > 0:
        coeffs = {v: int(c) for v, c in min_coeffs.items()}
        return {"coeffs": coeffs, "rel": ">=", "rhs": int(rhs)}
    coeffs = {v: int(-c) for v, c in min_coeffs.items()}
    return {"coeffs": coeffs, "rel": "<=", "rhs": int(-rhs)}


def display_text(disp: dict) -> str:
    """Render ``a·p_6 (>=|<=) <rest>`` with p_6 isolated on the left."""
    coeffs = _merge_tail_display(disp["coeffs"])   # §1.2 big_faces merge
    a = coeffs["p_6"]
    left = "p_6" if a == 1 else f"{a}*p_6"
    # a*p_6 + Σ_{v≠p6} c_v x_v  rel  rhs   ->   a*p_6  rel  rhs − Σ_{v≠p6} c_v x_v
    parts = []
    for v in DISPLAY_ORDER:
        if v == "p_6":
            continue
        c = coeffs.get(v, 0)
        if c == 0:
            continue
        name = PRETTY[v]
        rc = -c
        parts.append(name if rc == 1 else (f"-{name}" if rc == -1 else f"{rc}*{name}"))
    rhs = disp["rhs"]
    if rhs != 0 or not parts:
        parts.append(str(rhs))
    rhs_expr = " + ".join(parts).replace("+ -", "- ")
    return f"{left} {'>=' if disp['rel'] == '>=' else '<='} {rhs_expr}"


def _is_trivial(coeffs: dict, rhs: int) -> bool:
    # all coefficients non-negative and rhs <= 0  =>  always true
    if coeffs and all(c >= 0 for c in coeffs.values()) and rhs <= 0:
        return True
    if coeffs and all(c <= 0 for c in coeffs.values()) and rhs >= 0:
        return True
    return False


def _weakens_premise(coeffs: dict, rhs: int, premises: list) -> bool:
    """True if the (canonical) conclusion has the same LHS direction as some
    (canonical) premise and is no stronger than it."""
    ckey = tuple(sorted((v, Fraction(c)) for v, c in coeffs.items()))
    for pr in premises:
        pc = canonicalize({v: Fraction(c) for v, c in pr["coeffs"].items()})
        prim = D._primitive(pc, Fraction(-pr["rhs"]))
        if prim is None:
            continue
        ic, nc = prim
        if tuple(sorted((v, Fraction(c)) for v, c in ic.items())) == ckey and pr["rel"] == ">=":
            if rhs <= -nc:
                return True
    return False


# ── linear-derivability filter (§4) ──────────────────────────────────────────
def _unconditional_forms():
    """All unconditional inventory entries as (coeffs, const, rel) forms."""
    forms = []
    for e in INV.INVENTORY:
        if e["kind"] in ("equality", "inequality"):
            forms.append(D._conc_to_form(e["conclusion"]))
    return forms


def _premise_forms(premises):
    return [D._conc_to_form(pr) for pr in premises]


def _lp_min(obj_coeffs: dict, constraints):
    """Minimise ``obj_coeffs · x`` subject to the constraint forms
    ``coeffs·x + const rel 0`` over all atoms (free).  Returns the optimum
    (float) or ``None`` if unbounded below / infeasible."""
    idx = {v: i for i, v in enumerate(ALL_VARS)}
    n = len(ALL_VARS)
    A_ub, b_ub, A_eq, b_eq = [], [], [], []
    for coeffs, const, rel in constraints:
        row = [0.0] * n
        for v, c in coeffs.items():
            row[idx[v]] = float(c)
        if rel == "==":
            A_eq.append(row)
            b_eq.append(-float(const))
        else:                                  # ">=":  coeffs·x + const >= 0
            A_ub.append([-x for x in row])
            b_ub.append(float(const))
    c = [0.0] * n
    for v, coef in obj_coeffs.items():
        c[idx[v]] = float(coef)
    D.work_tick()                              # v0.6.5 §2: count this LP solve
    try:
        res = linprog(c, A_ub=A_ub or None, b_ub=b_ub or None,
                      A_eq=A_eq or None, b_eq=b_eq or None,
                      bounds=[(None, None)] * n, method="highs")
    except Exception:
        return None
    if not res.success or not np.isfinite(res.fun):
        return None
    return float(res.fun)


def _hyp_derivable(premises, hyp):
    """Is the conditional hypothesis ``hyp`` (``coeffs ≥ rhs``) linearly derivable
    from the premises and unconditional inventory?"""
    constraints = _premise_forms(premises) + _unconditional_forms()
    coeffs = {v: Fraction(c) for v, c in hyp["coeffs"].items()}
    m = _lp_min(coeffs, constraints)
    if m is None:
        return False
    return m - float(hyp["rhs"]) >= -_LP_TOL


def linearly_derivable(premises, conclusion) -> bool:
    """§4: the conclusion is linearly derivable iff the LP relaxation (premises +
    unconditional inventory + any conditional theorem whose hypothesis is itself
    linearly derivable) already forces it.  Such conclusions need no integer
    rounding or case split and are discarded."""
    constraints = _premise_forms(premises) + _unconditional_forms()
    for e in INV.CONDITIONAL_THEOREMS:
        if _hyp_derivable(premises, e["hypothesis"]):
            constraints.append(D._conc_to_form(e["conclusion"]))
    coeffs = {v: Fraction(c) for v, c in conclusion["coeffs"].items()}
    m = _lp_min(coeffs, constraints)
    if m is None:
        return False                           # unbounded -> not linearly forced
    return m - float(conclusion["rhs"]) >= -_LP_TOL


# ── candidate generation by direction enumeration (§2, v0.6.2) ────────────────
import itertools as _it
import time as _time
from math import ceil as _ceil

# split thresholds, aligned with the conditional theorems' hypotheses
#   (Jučovič: f_2 >= 7 ; Barnette: big_faces >= 3), plus the second level.
_SPLIT_THRESHOLDS = [("f_2", {"f_2": 1}, [7, 8]),
                     ("big_faces", dict(BIG_FACES), [3, 4])]
# directions: a*p_6 (a in {1,2}) plus up to two terms chosen from these atoms with
# coefficients in {-2,-1,1,2}.  v0.6.3 §2.5: the conclusion may only use
# p_3, p_4, p_5 and sum_pk_after_p6 (the tail); f_2 is excluded.
_DIR_TERMS = ["p_3", "p_4", "p_5", TAIL]
_DIR_COEFFS = (-2, -1, 1, 2)


def _term_vec(name, coeff):
    if name == "big_faces":
        return {v: coeff for v, c in BIG_FACES.items()}
    return {name: coeff}


def _coprime(d):
    """Divide an int-coeff dict by the gcd of its entries."""
    vals = [abs(int(c)) for c in d.values() if int(c) != 0]
    if not vals:
        return {}
    g = 0
    for v in vals:
        g = gcd(g, v)
    g = g or 1
    return {k: int(c) // g for k, c in d.items() if int(c) != 0}


def enumerate_directions():
    """§2: the direction set D.  Each direction has a positive p_6 coefficient."""
    seen, dirs = set(), []

    def add(base, terms):
        d = dict(base)
        for name, cf in terms:
            for v, c in _term_vec(name, cf).items():
                d[v] = d.get(v, 0) + c
        d = _coprime(d)
        if d.get("p_6", 0) <= 0:
            return                                   # keep p_6 on the LHS, a > 0
        key = tuple(sorted(d.items()))
        if key in seen:
            return
        seen.add(key)
        dirs.append(d)

    for a in (1, 2):
        base = {"p_6": a}
        add(base, [])
        for name in _DIR_TERMS:
            for cf in _DIR_COEFFS:
                add(base, [(name, cf)])
        for n1, n2 in _it.combinations(_DIR_TERMS, 2):
            for c1 in _DIR_COEFFS:
                for c2 in _DIR_COEFFS:
                    add(base, [(n1, c1), (n2, c2)])
    return dirs


_ALL_IDX = {v: i for i, v in enumerate(ALL_VARS)}
_NVARS = len(ALL_VARS)


def _prep_matrices(constraints):
    """Build the LP matrices (A_ub,b_ub,A_eq,b_eq) for a constraint set *once*;
    the objective vector is supplied per direction in :func:`_lp_pre`."""
    A_ub, b_ub, A_eq, b_eq = [], [], [], []
    for coeffs, const, rel in constraints:
        row = [0.0] * _NVARS
        for v, c in coeffs.items():
            row[_ALL_IDX[v]] = float(c)
        if rel == "==":
            A_eq.append(row)
            b_eq.append(-float(const))
        else:
            A_ub.append([-x for x in row])
            b_ub.append(float(const))
    return (np.array(A_ub) if A_ub else None, np.array(b_ub) if b_ub else None,
            np.array(A_eq) if A_eq else None, np.array(b_eq) if b_eq else None)


def _lp_pre(cvec, mats):
    """Solve min ``cvec·x`` for pre-built matrices; returns ('opt',v) /
    ('unbounded',None) / ('infeasible',None)."""
    A_ub, b_ub, A_eq, b_eq = mats
    D.work_tick()                              # v0.6.5 §2: count this LP solve
    try:
        res = linprog(cvec, A_ub=A_ub, b_ub=b_ub, A_eq=A_eq, b_eq=b_eq,
                      bounds=[(None, None)] * _NVARS, method="highs")
    except Exception:
        return ("infeasible", None)
    if res.status == 0 and np.isfinite(res.fun):
        return ("opt", float(res.fun))
    if res.status == 3:
        return ("unbounded", None)
    return ("infeasible", None)


def _lp_solve(obj_coeffs, constraints):
    """Minimise ``obj·x`` over the forms (direction-dependent; builds matrices
    on the fly — used by the non-hot paths)."""
    cvec = [0.0] * _NVARS
    for v, coef in obj_coeffs.items():
        cvec[_ALL_IDX[v]] = float(coef)
    return _lp_pre(cvec, _prep_matrices(constraints))


def _entailed_form(constraints, coeffs, rhs):
    """Is ``coeffs·x >= rhs`` forced by the LP over ``constraints``?"""
    st, v = _lp_solve(coeffs, constraints)
    return st == "opt" and v - float(rhs) >= -_LP_TOL


def _triggerable_conditionals(constraints):
    """Conditional-theorem conclusions whose hypothesis is entailed by the
    constraints (so they may be used in that branch)."""
    out = []
    for e in INV.CONDITIONAL_THEOREMS:
        h = e["hypothesis"]
        coeffs = {v: Fraction(c) for v, c in h["coeffs"].items()}
        if _entailed_form(constraints, coeffs, Fraction(h["rhs"])):
            out.append(D._conc_to_form(e["conclusion"]))
    return out


def _premise_entailed_lp(constraints, pr):
    """Is lemma premise ``pr`` ({coeffs, rel, rhs}) LP-forced by ``constraints``?"""
    cf = {v: Fraction(c) for v, c in pr["coeffs"].items()}
    rhs = Fraction(pr["rhs"])
    rel = pr["rel"]
    if rel == ">=":
        return _entailed_form(constraints, cf, rhs)
    if rel == "<=":
        return _entailed_form(constraints, {v: -c for v, c in cf.items()}, -rhs)
    if rel in ("=", "=="):
        return (_entailed_form(constraints, cf, rhs)
                and _entailed_form(constraints, {v: -c for v, c in cf.items()}, -rhs))
    return False


def _triggerable_lemmas(constraints):
    """v0.7 §1: library-lemma conclusions whose premises are all entailed by the
    constraints — usable as extra linear facts in that LP context (same role as a
    conditional theorem, now also in candidate detection)."""
    out = []
    for cnum in sorted(D.LEMMAS):
        lem = D.LEMMAS[cnum]
        if all(_premise_entailed_lp(constraints, pr) for pr in lem["premises"]):
            out.append((dict(lem["coeffs"]), lem["const"], lem["rel"]))
    return out


def _build_split_tree(prem_forms, assum_forms, depth):
    """§2.2: build the (direction-independent) case-split tree for a premise set.
    Each node carries the pre-built LP matrices of its leaf constraint set WITHOUT
    lemmas (``mats``) and WITH triggerable library lemmas added (``mats_lemma``, v0.7
    §1), plus ``(ge_child, le_child)`` splits on undecided thresholds.  Built once per
    premise set; ``_vint_eval`` picks which matrices to use per direction."""
    base = prem_forms + assum_forms + _unconditional_forms()
    leaf_base = base + _triggerable_conditionals(base)
    leaf_lemma = leaf_base + _triggerable_lemmas(base)
    node = {"mats": _prep_matrices(leaf_base),
            "mats_lemma": _prep_matrices(leaf_lemma), "splits": []}
    if depth > 0:
        for _label, expr, ths in _SPLIT_THRESHOLDS:
            ecoeffs = {v: Fraction(c) for v, c in expr.items()}
            neg = {v: -c for v, c in ecoeffs.items()}
            for c in ths:
                if _entailed_form(base, ecoeffs, c):
                    continue
                if _entailed_form(base, neg, -(c - 1)):
                    continue
                ge = _build_split_tree(
                    prem_forms, assum_forms + [(dict(expr), Fraction(-c), ">=")],
                    depth - 1)
                le = _build_split_tree(
                    prem_forms,
                    assum_forms + [({v: -x for v, x in expr.items()},
                                    Fraction(c - 1), ">=")], depth - 1)
                node["splits"].append((ge, le))
    return node


def _lp_pre_x(cvec, mats):
    """Like :func:`_lp_pre`, but also return the optimal vertex ``x`` (dict over
    ALL_VARS) when the status is ``opt`` (needed to pick branch-and-bound variables).
    Returns ``(status, value, x)``."""
    A_ub, b_ub, A_eq, b_eq = mats
    D.work_tick()
    try:
        res = linprog(cvec, A_ub=A_ub, b_ub=b_ub, A_eq=A_eq, b_eq=b_eq,
                      bounds=[(None, None)] * _NVARS, method="highs")
    except Exception:
        return ("infeasible", None, None)
    if res.status == 0 and np.isfinite(res.fun):
        return ("opt", float(res.fun), {v: float(res.x[_ALL_IDX[v]]) for v in ALL_VARS})
    if res.status == 3:
        return ("unbounded", None, None)
    return ("infeasible", None, None)


def _add_int_bound(mats, var, rel, k):
    """Return a copy of ``mats`` with one extra integer bound row ``var rel k``
    (rel in ``"<="`` / ``">="``), for a branch-and-bound sub-problem."""
    A_ub, b_ub, A_eq, b_eq = mats
    row = np.zeros(_NVARS)
    if rel == "<=":
        row[_ALL_IDX[var]] = 1.0; b = float(k)          # var <= k
    else:
        row[_ALL_IDX[var]] = -1.0; b = -float(k)        # -var <= -k  (var >= k)
    nA = np.vstack([A_ub, row]) if A_ub is not None else row.reshape(1, -1)
    nb = np.concatenate([b_ub, [b]]) if b_ub is not None else np.array([b])
    return (nA, nb, A_eq, b_eq)


_NO_SPLIT_PS = {"cond": 0, "bnb": 0, "maxdepth": 0}


def _branch_ps(r):
    return r[2] if (r[0] == "opt" and r[2]) else _NO_SPLIT_PS


def _split_combine(kind, rge, rle):
    """Predicted proof-structure stats for a split: this split (of ``kind``) plus the
    splits inside both branches; nesting depth = 1 + max branch depth."""
    pg, pl = _branch_ps(rge), _branch_ps(rle)
    return {"cond": (1 if kind == "cond" else 0) + pg["cond"] + pl["cond"],
            "bnb": (1 if kind == "bnb" else 0) + pg["bnb"] + pl["bnb"],
            "maxdepth": 1 + max(pg["maxdepth"], pl["maxdepth"])}


def _merge_branch_vals(rge, rle):
    """min of the two branch bounds (an infeasible branch is a vacuous case); None
    if both branches are infeasible/unbounded."""
    if rge[0] == "unbounded" or rle[0] == "unbounded":
        return None
    feas = [r[1] for r in (rge, rle) if r[0] == "opt"]
    return min(feas) if feas else None


def _vint_eval(node, cvec, depth, use_lemmas=False):
    """§2.3–2.4 + v0.6.6 §1 + v0.7 §1: strongest integer lower bound on direction
    ``cvec`` via conditional-theorem splits (pre-built) AND branch-and-bound splits,
    sharing nesting budget ``depth``.  ``use_lemmas`` picks the lemma-augmented leaf
    matrices (so the bound may use library lemmas as linear facts).  Returns
    ``(status, value, pstats)``."""
    mats = node["mats_lemma"] if (use_lemmas and "mats_lemma" in node) else node["mats"]
    st, val, xstar = _lp_pre_x(cvec, mats)
    if st == "unbounded":
        return ("unbounded", None, None)
    if st != "opt":
        return ("infeasible", None, None)
    best = _ceil(val - _LP_TOL)
    best_ps = dict(_NO_SPLIT_PS)
    if depth > 0:
        # conditional-theorem splits (direction-independent, pre-built)
        for ge, le in node["splits"]:
            rge = _vint_eval(ge, cvec, depth - 1, use_lemmas)
            rle = _vint_eval(le, cvec, depth - 1, use_lemmas)
            mv = _merge_branch_vals(rge, rle)
            if mv is not None and mv > best:
                best, best_ps = mv, _split_combine("cond", rge, rle)
        # branch-and-bound split on a fractional LP variable (direction-dependent)
        pick = D._bnb_pick_var(xstar)
        if pick is not None:
            var, fl = pick
            ge_node = {"mats": _add_int_bound(mats, var, ">=", fl + 1), "splits": []}
            le_node = {"mats": _add_int_bound(mats, var, "<=", fl), "splits": []}
            rge = _vint_eval(ge_node, cvec, depth - 1, use_lemmas)
            rle = _vint_eval(le_node, cvec, depth - 1, use_lemmas)
            mv = _merge_branch_vals(rge, rle)
            if mv is not None and mv > best:
                best, best_ps = mv, _split_combine("bnb", rge, rle)
    return ("opt", best, best_ps)


def _dir_cvec(direction):
    cvec = [0.0] * _NVARS
    for v, c in direction.items():
        cvec[_ALL_IDX[v]] = float(c)
    return cvec


def classify_depth(premises, direction_coeffs):
    """§2 (v0.6.2): label the deductive depth of a conclusion ``direction·x >= c``.
    ``rounding_only`` when ``v_int == ceil(v_lin)`` (plain rounding of the LP
    relaxation suffices); ``split_needed`` when the case split adds strictly more
    (``v_int > ceil(v_lin)``).  Diagnostic label only — never filters."""
    pf = _premise_forms(premises)
    lin_base = pf + _unconditional_forms()
    lin_mats = _prep_matrices(lin_base + _triggerable_conditionals(lin_base))
    cvec = _dir_cvec({v: int(c) for v, c in direction_coeffs.items()})
    slin, vlin = _lp_pre(cvec, lin_mats)
    tree = _build_split_tree(pf, [], D.DEFAULT_SPLIT_DEPTH)
    sint, vint, _ = _vint_eval(tree, cvec, D.DEFAULT_SPLIT_DEPTH)
    if sint != "opt" or slin != "opt":
        return "split_needed"
    return "rounding_only" if vint == _ceil(vlin - _LP_TOL) else "split_needed"


def enumerate_candidates(premises, stats, rng, accept="split_needed"):
    """§2: produce candidate conclusions ``{coeffs, rel:'>=', rhs}`` by enumerating
    directions and, for each, comparing the LP relaxation bound ``v_lin`` with the
    integer / case-split bound ``v_int``.  A direction is a candidate iff
    ``v_int > v_lin`` (it genuinely needs rounding or a case split).  The split
    tree and the relaxation matrices are built once per premise set.

    ``accept`` (``"split_needed"`` | ``"rounding_only"``) keeps only directions of
    that deductive depth; the other type is dropped here (reason
    ``rounding_only_skipped`` / ``split_needed_skipped``) before any expensive proof
    reconstruction, exactly as v0.6.3 dropped rounding_only via REQUIRE_SPLIT."""
    pf = _premise_forms(premises)
    # v_lin matrices (relaxation: unconditional + triggerable conditionals + lemmas,
    # v0.7 §1.3 — so "linear_only" means derivable on top of the lemmas), once
    lin_base = pf + _unconditional_forms()
    lin_mats = _prep_matrices(lin_base + _triggerable_conditionals(lin_base)
                              + _triggerable_lemmas(lin_base))
    tree = _build_split_tree(pf, [], D.DEFAULT_SPLIT_DEPTH)       # once (both leaf mats)

    directions = enumerate_directions()
    rng.shuffle(directions)
    stats["directions_total"] += len(directions)
    t0 = _time.time()
    out, n_done = [], 0
    for d in directions:
        n_done += 1
        cvec = _dir_cvec(d)
        slin, vlin = _lp_pre(cvec, lin_mats)
        if slin != "opt":
            continue                                # unbounded / infeasible: skip
        # v0.7 §1.2: the bound uses lemmas (v_int_lemma); v_int_base (no lemmas) is
        # kept to gate the dependency check cheaply (§2).
        sint, vint, vps = _vint_eval(tree, cvec, D.DEFAULT_SPLIT_DEPTH, use_lemmas=True)
        if sint != "opt":
            continue
        if vint > vlin + _LP_TOL:
            dtype = "rounding_only" if vint == _ceil(vlin - _LP_TOL) else "split_needed"
            if dtype != accept:
                stats["rounding_only_skipped" if dtype == "rounding_only"
                      else "split_needed_skipped"] += 1
                continue
            sb, vint_base, _ = _vint_eval(tree, cvec, D.DEFAULT_SPLIT_DEPTH, use_lemmas=False)
            out.append({"coeffs": dict(d), "rel": ">=", "rhs": int(vint),
                        "pred_ps": vps, "v_int_lemma": int(vint),
                        "v_int_base": (int(vint_base) if sb == "opt" else None)})
        else:
            stats["linear_only"] += 1
    stats["directions_evaluated"] += n_done

    # Dedup to canonical (f_2-eliminated) lower bounds and apply the cheap LP
    # pre-filters (upper bound / p_6 padding) here, so the expensive deducer
    # reconstruction only runs on genuinely distinct viable candidates.
    best_by_canon = {}
    for cand in out:
        canon = canonicalize({v: Fraction(c) for v, c in cand["coeffs"].items()})
        prim = D._primitive(canon, Fraction(-cand["rhs"]))
        if prim is None:
            continue
        ic, nc = prim
        if nc.denominator != 1:
            continue
        cic = {v: int(x) for v, x in ic.items()}
        crhs = int(-nc)
        if not ALLOW_UPPER_BOUNDS and cic.get("p_6", 0) <= 0:
            stats["p6_upper_bound"] += 1
            continue
        if any(abs(c) > MAX_COEFF for c in cic.values()):
            continue
        key = tuple(sorted(cic.items()))
        prev = best_by_canon.get(key)
        if prev is None or crhs > prev["rhs"]:
            best_by_canon[key] = {"coeffs": cic, "rel": ">=", "rhs": crhs,
                                  "pred_ps": cand.get("pred_ps", _NO_SPLIT_PS),
                                  "v_int_lemma": cand.get("v_int_lemma"),
                                  "v_int_base": cand.get("v_int_base")}
    viable = []
    for cand in best_by_canon.values():
        cic, crhs = cand["coeffs"], cand["rhs"]
        lprime = {v: x for v, x in cic.items() if v != "p_6"}
        if not lprime:
            padded = crhs <= 0
        else:
            st, vr, _ = _vint_eval(tree, _dir_cvec(lprime), D.DEFAULT_SPLIT_DEPTH,
                                   use_lemmas=True)
            padded = (st == "opt" and vr >= crhs)
        if padded:
            stats["p6_padding"] += 1
            continue
        viable.append(cand)
    stats["enum_time"] += _time.time() - t0
    stats["enum_samples"] += 1
    return viable


# ── premise simplification (§1, v0.5) ─────────────────────────────────────────
def _premise_nonneg_forms(premises):
    """Premise forms plus non-negativity of the count variables (used for the
    'combined with non-negativity' reasoning of §1)."""
    cons = [D._conc_to_form(pr) for pr in premises]
    for v in list(INV.NONNEG_VARS) + ["f_2"]:
        cons.append(({v: Fraction(1)}, Fraction(0), ">="))
    return cons


def _lp_max(var, constraints):
    """Maximum of ``var`` over ``constraints`` (float), or None if unbounded."""
    m = _lp_min({var: Fraction(-1)}, constraints)
    return None if m is None else -m


def _entailed_by(pr, others):
    """Is premise ``pr`` implied by ``others`` + non-negativity?"""
    cons = _premise_nonneg_forms(others)
    coeffs = {v: Fraction(c) for v, c in pr["coeffs"].items()}
    rhs = float(pr["rhs"])
    lo = _lp_min(coeffs, cons)          # min of coeffs.x
    hi = _lp_max_expr(coeffs, cons)     # max of coeffs.x
    if pr["rel"] == ">=":
        return lo is not None and lo >= rhs - _LP_TOL
    if pr["rel"] == "<=":
        return hi is not None and hi <= rhs + _LP_TOL
    # "="
    return (lo is not None and lo >= rhs - _LP_TOL
            and hi is not None and hi <= rhs + _LP_TOL)


def _lp_max_expr(coeffs, constraints):
    m = _lp_min({v: -c for v, c in coeffs.items()}, constraints)
    return None if m is None else -m


def simplify_premises(premises):
    """§1: if the premises (with non-negativity) force a variable to 0, add it as
    an explicit ``x = 0`` and drop premises that thereby become redundant.  The
    result is equivalent to the input over the non-negative integers."""
    prem = [dict(p) for p in premises]

    def explicit_zero(v):
        return any(set(k for k, c in p["coeffs"].items() if c) == {v}
                   and p["rel"] == "=" and int(p["rhs"]) == 0 for p in prem)

    changed = True
    while changed:
        changed = False
        # (a) make an implied zero explicit
        cons = _premise_nonneg_forms(prem)
        for v in INV.NONNEG_VARS:
            if explicit_zero(v):
                continue
            mx = _lp_max(v, cons)
            if mx is not None and mx <= _LP_TOL:
                prem.append({"coeffs": {v: 1}, "rel": "=", "rhs": 0,
                             "text": f"{v} = 0"})
                changed = True
                break
        if changed:
            continue
        # (b) drop a premise implied by the others
        for i in range(len(prem)):
            if _entailed_by(prem[i], prem[:i] + prem[i + 1:]):
                del prem[i]
                changed = True
                break
    return prem


# ── integer MILP over the Inventory model (§3 gate v0.5, §2 arith-sharp v0.6.1) ─
# Variables = ALL_VARS followed by one binary per conditional theorem (the
# "hypothesis-false" branch of its big-M disjunction).  Built generically from
# the inventory so it tracks the variable set automatically.
_CM_IDX = {v: i for i, v in enumerate(ALL_VARS)}
_NCOND = len(INV.CONDITIONAL_THEOREMS)
_CM_N = len(ALL_VARS) + _NCOND
_CM_BIGM = 10 ** 7
# non-negativity for the count variables; W_tail/J_tail bounded generously
_NONNEG = set(INV.NONNEG_VARS)


def _cm_row(d):
    r = [0.0] * _CM_N
    for k, v in d.items():
        r[_CM_IDX[k]] += float(v)
    return r


def _cm_base_constraints():
    """Unconditional inventory + conditional big-M disjunctions."""
    cons = []
    for e in INV.INVENTORY:
        if e["kind"] in ("equality", "inequality"):
            co, k, rel = D._conc_to_form(e["conclusion"])   # co.x + k rel 0
            row = _cm_row(co)
            if rel == "==":
                cons.append((row, -float(k), -float(k)))
            else:                                            # >= 0
                cons.append(([-x for x in row], None, float(k)))
    for bi, e in enumerate(INV.CONDITIONAL_THEOREMS):
        b = len(ALL_VARS) + bi
        hc, hk, _ = D._conc_to_form(e["hypothesis"])         # hyp: hc.x + hk >= 0
        # hypothesis-false branch (binary b = 1):  hc.x <= -hk - 1 ... modelled as
        #   hyp_lhs <= (rhs-1) + M*(1-b)  where hyp is  hyp_lhs >= rhs
        hyp_rhs = float(e["hypothesis"]["rhs"])
        hyp_lhs = {v: Fraction(c) for v, c in e["hypothesis"]["coeffs"].items()}
        row = _cm_row(hyp_lhs); row[b] = _CM_BIGM
        cons.append((row, None, (hyp_rhs - 1) + _CM_BIGM))
        # conclusion branch (b = 0): conclusion holds
        cco, cck, _ = D._conc_to_form(e["conclusion"])       # cco.x + cck >= 0
        row = _cm_row(cco); row[b] = _CM_BIGM
        cons.append((row, -float(cck), None))
    return cons


def _cm_premise_rows(premises):
    out = []
    for pr in premises:
        rr = _cm_row(pr["coeffs"]); rhs = float(pr["rhs"])
        if pr["rel"] == "=":
            out.append((rr, rhs, rhs))
        elif pr["rel"] == ">=":
            out.append((rr, rhs, None))
        else:
            out.append((rr, None, rhs))
    return out


def _cm_bounds():
    bl = [0.0] * _CM_N
    bu = [0.0] * _CM_N
    for v, i in _CM_IDX.items():
        if v in _NONNEG:
            bl[i], bu[i] = 0.0, 10 ** 5
        else:                                 # W_tail, J_tail
            bl[i], bu[i] = -10 ** 6, 10 ** 6
    for bi in range(_NCOND):
        bl[len(ALL_VARS) + bi], bu[len(ALL_VARS) + bi] = 0.0, 1.0
    return np.array(bl), np.array(bu)


def _cm_solve(cons, objective=None):
    A = np.array([c[0] for c in cons])
    lb = np.array([-np.inf if c[1] is None else c[1] for c in cons])
    ub = np.array([np.inf if c[2] is None else c[2] for c in cons])
    bl, bu = _cm_bounds()
    obj = np.zeros(_CM_N) if objective is None else np.array(objective)
    D.work_tick()                              # v0.6.5 §2: count this MILP solve
    try:
        return milp(c=obj, constraints=[LinearConstraint(A, lb, ub)],
                    integrality=np.ones(_CM_N), bounds=Bounds(bl, bu))
    except Exception:
        return None


def counter_model(premises, conclusion):
    """§3 gate: integer point satisfying premises + all Inventory conditions +
    NEGATION of conclusion.  Returns the solution dict if found (a bug), else None."""
    cons = _cm_base_constraints() + _cm_premise_rows(premises)
    rr = _cm_row({v: Fraction(c) for v, c in conclusion["coeffs"].items()})
    rhs = float(conclusion["rhs"])
    if conclusion["rel"] == ">=":
        cons.append((rr, None, rhs - 1))
    else:
        cons.append((rr, rhs + 1, None))
    res = _cm_solve(cons)
    if res is not None and res.success and res.x is not None:
        return {v: int(round(res.x[i])) for v, i in _CM_IDX.items()}
    return None


def arith_min(premises, conclusion):
    """§2 (v0.6.1): minimise the conclusion LHS over premises + Inventory (integer).
    Returns the minimum (int) or None if unbounded/infeasible."""
    cons = _cm_base_constraints() + _cm_premise_rows(premises)
    obj = [0.0] * _CM_N
    for v, c in conclusion["coeffs"].items():
        obj[_CM_IDX[v]] = float(c)
    res = _cm_solve(cons, obj)
    if res is None or not res.success or res.x is None:
        return None
    return int(round(float(res.fun)))


# ── bound strengthening (§2 of v0.2) + redundant-term removal (§3 of v0.3) ────
_NONNEG_FACESPLIT = None


def _nonneg_facesplit_forms():
    global _NONNEG_FACESPLIT
    if _NONNEG_FACESPLIT is None:
        forms = []
        for e in INV.INVENTORY:
            if e["name"] == "face_split" or e["name"].startswith("nonneg_"):
                forms.append(D._conc_to_form(e["conclusion"]))
        _NONNEG_FACESPLIT = forms
    return _NONNEG_FACESPLIT


def _implies_via_base(frm: dict, to: dict) -> bool:
    """Does ``frm`` (``coeffs ≥ rhs``) imply ``to`` using only non-negativity and
    face_split?  (LP: is ``to`` forced by ``frm`` + those base facts.)"""
    constraints = [D._conc_to_form(frm)] + _nonneg_facesplit_forms()
    coeffs = {v: Fraction(c) for v, c in to["coeffs"].items()}
    m = _lp_min(coeffs, constraints)
    if m is None:
        return False
    return m - float(to["rhs"]) >= -_LP_TOL


def _strongest_in(ctx, direction: dict):
    """Strongest provable bound for ``direction`` read off an *already saturated*
    pool (§4.2: reuse the fact pool instead of re-deriving).  Returns
    ``(conclusion, fact)`` or None."""
    Ldir = {v: int(c) for v, c in direction.items() if int(c) != 0}
    if not Ldir:
        return None
    fact = _find_fact(ctx, {"coeffs": Ldir, "rel": ">=", "rhs": -10 ** 9})
    if fact is None:
        return None
    prim = _primitive_int(fact.coeffs, fact.const)
    if prim is None or prim[1].denominator != 1:
        return None
    ic, nc = prim
    return {"coeffs": ic, "rel": ">=", "rhs": int(-nc)}, fact


def _neg(d):
    return {v: -int(c) for v, c in d.items() if int(c) != 0}


def _strongest(pruned, direction: dict):
    """Strongest provable bound for ``direction`` over ``pruned`` — the deducer
    saturates with ``direction`` added (v0.6.2: candidates are arbitrary
    directions, not in the base set)."""
    Ldir = {v: int(c) for v, c in direction.items() if int(c) != 0}
    if not Ldir:
        return None
    ctx = cached_context(pruned, [Ldir, _neg(Ldir)])
    r = _strongest_in(ctx, direction)
    if r is None:
        return None
    concl, fact = r
    return concl, ctx, fact


def strengthen_and_simplify(conclusion0: dict, pruned: list, use_lemmas=True):
    """§2: strengthen to the strongest provable constant; §3-v0.3: then greedily
    drop any non-p_6 term whose removal still yields a provable (and, via nonneg +
    face_split, stronger-or-equivalent) conclusion.  The deducer saturates once
    with the conclusion direction and all single-term-drop directions added.
    ``use_lemmas`` (v0.7) lets the proof use library lemmas.
    Returns ``(conclusion, ctx, fact)`` or None."""
    d0 = {v: int(c) for v, c in conclusion0["coeffs"].items() if int(c) != 0}
    dirs = [d0, _neg(d0)]
    for x in [v for v in d0 if v != "p_6"]:
        red = {v: c for v, c in d0.items() if v != x}
        if "p_6" in red:
            dirs += [red, _neg(red)]
    ctx = cached_context(pruned, dirs, use_lemmas=use_lemmas)
    r = _strongest_in(ctx, conclusion0["coeffs"])
    if r is None:
        return None
    cur, fact = r
    changed = True
    while changed:
        changed = False
        for x in [v for v in cur["coeffs"] if v != "p_6"]:
            reduced = {v: c for v, c in cur["coeffs"].items() if v != x}
            if "p_6" not in reduced:
                continue
            rr = _strongest_in(ctx, reduced)
            if rr is None:
                continue
            red_concl, rfact = rr
            if _implies_via_base(red_concl, cur):
                cur, fact = red_concl, rfact
                changed = True
                break
    return cur, ctx, fact


# ── cost-bounded re-proving: shortest proof (§1, v0.6.7) ──────────────────────
# Search grid of method restrictions (depth × which split kinds are allowed),
# ordered cheapest-feature first.  (3, True, True) == the unrestricted initial
# proof and is omitted.  Varying BOTH depth and split-kind satisfies "not only the
# nesting-depth dimension".  The grid is fixed, so the search is deterministic.
_SHORTEN_CONFIGS = [
    (0, False, False),                                   # no case split at all
    (1, True, False), (1, False, True), (1, True, True),  # depth 1
    (2, True, False), (2, False, True), (2, True, True),  # depth 2
    (3, True, False), (3, False, True),                   # depth 3 (single kind)
]


def _reprove(pruned, conclusion, depth, use_cond, use_bnb, use_lemmas=True):
    """Re-derive ``conclusion`` under the given method restrictions.  Returns
    ``(ctx, fact, tb, cost)`` if the SAME (or stronger) bound is provable, else None."""
    d0 = {v: int(c) for v, c in conclusion["coeffs"].items() if int(c) != 0}
    if not d0:
        return None
    ctx = Context(premises=pruned, depth=depth, extra_directions=[d0, _neg(d0)],
                  use_conditional_split=use_cond, use_bnb=use_bnb, use_lemmas=use_lemmas)
    ctx.saturate()
    fact = _find_fact(ctx, conclusion)
    if fact is None:
        return None
    tb = traceback(ctx, fact)
    return ctx, fact, tb, HARD.proof_difficulty(tb)


def shortest_lemma_free(pruned, conclusion):
    """§3.2 (v0.7): the cheapest proof that uses NO lemmas, over the shorten grid plus
    the full-feature config.  Returns ``(tb, ctx, fact, cost)`` or None if the
    conclusion is not provable without lemmas."""
    best = None
    for depth, uc, ub in _SHORTEN_CONFIGS + [(D.DEFAULT_SPLIT_DEPTH, True, True)]:
        try:
            r = _reprove(pruned, conclusion, depth, uc, ub, use_lemmas=False)
        except D.WorkBudgetExceeded:
            break
        if r is None:
            continue
        if best is None or r[3] < best[3]:
            best = r
    return best


def shorten_proof(pruned, conclusion, tb, ctx, fact, init_cost, use_lemmas=True):
    """§1 (v0.6.7): AlphaGeometry-style proof pruning.  Re-prove ``conclusion`` under
    a grid of method restrictions and keep the lowest-cost proof, iterating up to
    MAX_SHORTEN_ROUNDS times (each round adopts any strictly-cheaper proof).  Returns
    ``(tb, ctx, fact, cost, rounds)``.  Work is counted in the per-group budget; if
    the budget is hit mid-search the best proof found so far is kept (the already
    sound+verified conjecture is never discarded by the shortening step).  v0.7:
    ``use_lemmas`` keeps library lemmas available during the search."""
    best = (tb, ctx, fact, init_cost)
    # §1.4: a proof with no case split is already structurally minimal — skip it.
    if HARD.proof_structure_stats(tb)["case_splits"] == 0:
        return best[0], best[1], best[2], best[3], 0
    rounds = 0
    try:
        for _ in range(MAX_SHORTEN_ROUNDS):
            improved = False
            for depth, use_cond, use_bnb in _SHORTEN_CONFIGS:
                r = _reprove(pruned, conclusion, depth, use_cond, use_bnb,
                             use_lemmas=use_lemmas)
                if r is None:
                    continue
                if r[3] < best[3]:                       # strictly cheaper proof
                    best = (r[2], r[0], r[1], r[3])
                    improved = True
            if improved:
                rounds += 1
            else:
                break
    except D.WorkBudgetExceeded:
        pass                                             # keep the best proof so far
    return best[0], best[1], best[2], best[3], rounds


# ── premise de-duplication (§1) ──────────────────────────────────────────────
def _premise_implies(a: dict, b: dict) -> bool:
    """Does premise ``a`` imply premise ``b`` (so ``b`` is redundant)?  Handled
    for premises on the same single canonical LHS direction."""
    ca = canonicalize({v: Fraction(c) for v, c in a["coeffs"].items()})
    cb = canonicalize({v: Fraction(c) for v, c in b["coeffs"].items()})
    pa, pb = D._primitive(ca, Fraction(-a["rhs"])), D._primitive(cb, Fraction(-b["rhs"]))
    if pa is None or pb is None:
        return False
    ia, na = pa
    ib, nb = pb
    # equalities imply same-LHS inequalities in either direction
    if a["rel"] == "=":
        if tuple(sorted(ia.items())) == tuple(sorted(ib.items())):
            if b["rel"] == ">=" and -na >= -nb:
                return True
            if b["rel"] == "<=" and na >= nb:
                return True
            if b["rel"] == "=" and na == nb:
                return True
        neg = {v: -c for v, c in ia.items()}
        if tuple(sorted(neg.items())) == tuple(sorted(ib.items())) and b["rel"] == ">=":
            if na >= -nb:
                return True
    if a["rel"] == b["rel"] == ">=" and tuple(sorted(ia.items())) == tuple(sorted(ib.items())):
        return -na >= -nb                      # a is the stronger lower bound
    if a["rel"] == b["rel"] == "<=" and tuple(sorted(ia.items())) == tuple(sorted(ib.items())):
        return na >= nb                        # a is the stronger upper bound
    return False


def dedup_premises(premises: list) -> list:
    """Drop any premise implied by another in the same group (§1)."""
    keep = list(premises)
    changed = True
    while changed:
        changed = False
        for i, b in enumerate(keep):
            for j, a in enumerate(keep):
                if i == j:
                    continue
                if _premise_implies(a, b) and not (
                        _premise_implies(b, a) and j > i):
                    del keep[i]
                    changed = True
                    break
            if changed:
                break
    return keep


# ── premise minimization (§3) ────────────────────────────────────────────────
def _derives(ctx: Context, conclusion: dict) -> bool:
    """Can ``ctx`` derive the conclusion (same or stronger), compared on the
    canonical form so f_2 ↔ p-vars rewrites don't matter?"""
    return _find_fact(ctx, conclusion) is not None


def minimize_premises(premises: list, conclusion: dict) -> list:
    """Greedy pruning (AlphaGeometry-2 style): drop a premise permanently if the
    conclusion is still derivable without it."""
    kept = list(premises)
    i = 0
    while i < len(kept):
        trial = kept[:i] + kept[i + 1:]
        ctx = cached_context(trial)
        if _derives(ctx, conclusion):
            kept = trial                       # premise unnecessary -> drop
        else:
            i += 1
    return kept


def harvest_conjectures(ctx: Context, premises: list) -> list:
    """Return candidate ``(conclusion, fact)`` pairs from a saturated context.
    All filters are evaluated on the canonical form (f_2 eliminated)."""
    out = []
    seen_lhs = {}
    for fact in ctx.all_prop_facts():
        prim = _primitive_int(fact.coeffs, fact.const)
        if prim is None:
            continue
        icoeffs, nc = prim
        if nc.denominator != 1:
            continue                      # not integer-rounded -> skip
        rhs = int(-nc)
        canon = canonicalize({v: Fraction(c) for v, c in icoeffs.items()})
        cprim = D._primitive(canon, Fraction(-rhs))
        if cprim is None:
            continue
        cic, cnc = cprim
        canon_int = {v: int(c) for v, c in cic.items()}
        canon_rhs = int(-cnc)
        # (a) p_6 must survive BOTH in the canonical form (f_2 eliminated) and
        #     in the minimal equivalent form (§1, v0.3 — both checks required)
        if canon_int.get("p_6", 0) == 0:
            continue
        if not minimal_has_p6({v: Fraction(c) for v, c in icoeffs.items()}):
            continue
        # (b) max coeff <= 6 (display form)
        if any(abs(c) > MAX_COEFF for c in icoeffs.values()):
            continue
        # (c) non-trivial in canonical form
        if _is_trivial(canon_int, canon_rhs):
            continue
        conclusion = {"coeffs": icoeffs, "rel": ">=", "rhs": rhs}
        lhs = tuple(sorted(canon_int.items()))
        if lhs in seen_lhs and seen_lhs[lhs] >= rhs:
            continue
        seen_lhs[lhs] = rhs
        out.append((conclusion, fact))
    return out


# ── finding a proof fact after minimization ──────────────────────────────────
def _canon_index(ctx: Context):
    """Build (once, cached on the context) a map from canonical-LHS key to the
    strongest pool fact with that LHS.  Makes :func:`_find_fact` O(1)."""
    idx = getattr(ctx, "_canon_idx", None)
    if idx is not None:
        return idx
    idx = {}
    for fact in ctx.all_prop_facts():
        prim = D._primitive(canonicalize(fact.coeffs), fact.const)
        if prim is None:
            continue
        ic, nc = prim
        if nc.denominator != 1:
            continue
        key = tuple(sorted((v, int(c)) for v, c in ic.items()))
        prev = idx.get(key)
        if prev is None or -nc > prev[1]:
            idx[key] = (fact, -nc)
    ctx._canon_idx = idx
    return idx


def _find_fact(ctx: Context, conclusion: dict):
    """Return the strongest pool fact whose *canonical* LHS matches the
    conclusion's canonical LHS with a bound at least as strong, or None."""
    target = canonicalize({v: Fraction(c) for v, c in conclusion["coeffs"].items()})
    pt = D._primitive(target, Fraction(-conclusion["rhs"]))
    if pt is None:
        return None
    it, nt = pt
    key_t = tuple(sorted((v, int(c)) for v, c in it.items()))
    hit = _canon_index(ctx).get(key_t)
    if hit is not None and hit[1] >= -nt:
        return hit[0]
    return None


# ── hashing (dedup) — on canonical (f_2-eliminated) forms ─────────────────────
def premise_key(premises: list):
    items = []
    for pr in premises:
        pc = canonicalize({v: Fraction(c) for v, c in pr["coeffs"].items()})
        prim = D._primitive(pc, Fraction(-pr["rhs"]))
        if prim is None:
            key = ((), str(pr["rhs"]), pr["rel"])
        else:
            ic, nc = prim
            key = (tuple(sorted((v, int(c)) for v, c in ic.items())), str(nc), pr["rel"])
        items.append(key)
    return frozenset(items)


def conjecture_hash(premises: list, conclusion: dict):
    canon = canonicalize({v: Fraction(c) for v, c in conclusion["coeffs"].items()})
    prim = D._primitive(canon, Fraction(-conclusion["rhs"]))
    if prim is None:
        ckey = ((), conclusion["rel"], conclusion["rhs"])
    else:
        ic, nc = prim
        ckey = (tuple(sorted((v, int(c)) for v, c in ic.items())), conclusion["rel"],
                str(nc))
    return (premise_key(premises), ckey)


def select_lemma_library(record_dir: Path):
    """v0.7 §1: choose the lemma library from the existing record.  Eligible = at most
    2 premises and ``attained == "yes"``.  If more than LEMMA_LIB_MAX qualify, keep the
    first LEMMA_LIB_MAX by: fewer premises → more touch → higher hardness → smaller C.

    Returns ``(lemmas, lemma_meta, lemma_data)``:
      lemmas     cnum -> {premises, coeffs(Fraction), const(Fraction), rel} for the deducer
      lemma_meta cnum -> {generation, proof_cost_expanded}
      lemma_data cnum -> full record json (for inlining into Lean)."""
    cand = []
    if record_dir.exists():
        for d in sorted(record_dir.iterdir()):
            j = d / f"{d.name}.json"
            if not j.exists():
                continue
            data = json.load(open(j))
            cj = data["conjecture"]
            if len(cj["premises"]) > 2 or data.get("attained") != "yes":
                continue
            cand.append((int(d.name[1:]), data))
    # deterministic ordering, then cap
    cand.sort(key=lambda t: (len(t[1]["conjecture"]["premises"]),
                             -(t[1].get("touch") or 0),
                             -t[1].get("hardness", 0.0), t[0]))
    cand = cand[:LEMMA_LIB_MAX]
    lemmas, lemma_meta, lemma_data = {}, {}, {}
    for cnum, data in cand:
        cj = data["conjecture"]
        concl = cj["conclusion"]
        lemmas[cnum] = {"premises": cj["premises"],
                        "coeffs": {k: Fraction(v) for k, v in concl["coeffs"].items()},
                        "const": Fraction(-int(concl["rhs"])), "rel": ">="}
        lemma_meta[cnum] = {"generation": data.get("generation", 0),
                            "proof_cost_expanded": data.get("proof_cost_expanded",
                                                            data.get("proof_cost", 0.0))}
        lemma_data[cnum] = data
    return lemmas, lemma_meta, lemma_data


def load_existing_hashes(record_dir: Path):
    """Recompute hashes from existing record json (hash is never stored)."""
    hashes = {}
    max_id = 0
    if not record_dir.exists():
        return hashes, max_id
    for d in record_dir.iterdir():
        j = d / f"{d.name}.json"
        if not j.exists():
            continue
        with open(j) as fh:
            data = json.load(fh)
        cj = data["conjecture"]
        h = conjecture_hash(cj["premises"], cj["conclusion"])
        hashes[h] = d.name
        try:
            max_id = max(max_id, int(d.name[1:]))
        except ValueError:
            pass
    return hashes, max_id


# ── skeleton de-duplication (§1/§2, v0.6) ─────────────────────────────────────
# A skeleton abstracts a conjecture to its structure, replacing constants by a
# placeholder, so conjectures that differ only in constants collapse together.
def _skel_lhs(coeffs):
    """Coprime-integer coefficient tuple (sign preserved) — the structural LHS."""
    nz = {v: Fraction(c) for v, c in coeffs.items() if Fraction(c) != 0}
    prim = D._primitive(nz, Fraction(0))
    if prim is None:
        return ()
    ic, _ = prim
    return tuple(sorted((v, int(c)) for v, c in ic.items()))


def premise_skeleton(pr):
    """Keep variables/coeffs/relation; replace the constant by a placeholder,
    EXCEPT keep ``x = 0`` (an '='-premise, which is structural)."""
    lhs = _skel_lhs(pr["coeffs"])
    if pr["rel"] == "=":
        return (lhs, "=", int(pr["rhs"]))        # structural (x = 0): keep 0
    return (lhs, pr["rel"], "*")                 # placeholder for the constant


def conclusion_skeleton(conclusion):
    canon = canonicalize({v: Fraction(c) for v, c in conclusion["coeffs"].items()})
    return (_skel_lhs(canon), conclusion["rel"])


def conjecture_skeleton(premises, conclusion):
    return (frozenset(premise_skeleton(pr) for pr in premises),
            conclusion_skeleton(conclusion))


def skeleton_better(new: dict, old: dict) -> bool:
    """Is ``new`` strictly better than ``old`` (same skeleton)?  Order:
    attained(yes>unknown), then touch (only when attained), then hardness."""
    rank = lambda a: 1 if a == "yes" else 0
    if rank(new["attained"]) != rank(old["attained"]):
        return rank(new["attained"]) > rank(old["attained"])
    if new["attained"] == "yes":
        nt, ot = (new["touch"] or 0), (old["touch"] or 0)
        if nt != ot:
            return nt > ot
    ns, os_ = bool(new.get("arith_sharp")), bool(old.get("arith_sharp"))
    if ns != os_:
        return ns and not os_          # arith_sharp true beats false
    if new["hardness"] != old["hardness"]:
        return new["hardness"] > old["hardness"]
    return False


def build_skeleton_index(record_dir: Path, features):
    """Map skeleton -> info about the best recorded conjecture with that skeleton."""
    idx = {}
    if not record_dir.exists():
        return idx
    for d in sorted(record_dir.iterdir()):
        j = d / f"{d.name}.json"
        if not j.exists():
            continue
        data = json.load(open(j))
        cj = data["conjecture"]
        skel = conjecture_skeleton(cj["premises"], cj["conclusion"])
        att = data.get("attained", "yes")
        touch = data.get("touch")
        if touch is None and att == "yes":
            touch = IRIS.iris_score(cj["premises"], cj["conclusion"],
                                    features)["touch_size"]
        idx[skel] = {"name": d.name, "attained": att, "touch": touch,
                     "arith_sharp": data.get("arith_sharp", False),
                     "hardness": data["hardness"], "formula": cj["formula"],
                     "supersedes": data.get("supersedes", [])}
    return idx


# ── soundness regression ─────────────────────────────────────────────────────
def soundness_check(premises: list, conclusion: dict, pvecs: list, pvec_vars: list):
    """Raise if any real p-vector satisfies the premises but violates the
    conclusion (indicates a bug in inventory or deducer)."""
    ccoeffs = {v: Fraction(c) for v, c in conclusion["coeffs"].items()}
    crhs = Fraction(conclusion["rhs"])
    for pv, vals in zip(pvecs, pvec_vars):
        if not _pvec_satisfies(vals, premises):
            continue
        lhs = sum(c * vals.get(v, 0) for v, c in ccoeffs.items())
        ok = lhs >= crhs if conclusion["rel"] == ">=" else lhs <= crhs
        if not ok:
            raise AssertionError(
                f"SOUNDNESS VIOLATION: p-vector {pv} satisfies premises "
                f"{premises} but violates conclusion {conclusion} "
                f"(lhs={lhs}, rhs={crhs})")


# ── natural language / formula rendering ─────────────────────────────────────
def _render_ineq_text(coeffs: dict, rel: str, rhs: int) -> str:
    coeffs = _merge_tail_display(coeffs)           # §1.2 big_faces merge
    parts = []
    for v in DISPLAY_ORDER:
        c = coeffs.get(v, 0)
        if c == 0:
            continue
        name = PRETTY[v]
        parts.append(name if c == 1 else (f"-{name}" if c == -1 else f"{c}*{name}"))
    lhs = " + ".join(parts).replace("+ -", "- ") if parts else "0"
    sym = {">=": ">=", "<=": "<=", "=": "="}[rel]
    return f"{lhs} {sym} {rhs}"


# ── OLD_REPO-format formula string (v0.6.3 §2) ────────────────────────────────
# Conclusions use p3/p4/p5/p6 (no underscore) and sum_pk_after_p6, p_6 normalised
# to coefficient 1, %.10g decimal coefficients and a nested-parenthesis fold,
# matching the original repository, e.g.
#   if ((is_simple) and (p_4 = 0) and (p_5 <= 2) and (f_2>=_7)),
#       then p6 >= (((-0.5 * sum_pk_after_p6) + 2))
_OLD_NAME = {"p_3": "p3", "p_4": "p4", "p_5": "p5", "p_6": "p6",
             "sum_pk_after_p6": "sum_pk_after_p6"}


def _old_num(x) -> str:
    return f"{float(x):.10g}"


def _old_premise(pr: dict) -> str:
    coeffs = {v: int(c) for v, c in pr["coeffs"].items() if c}
    # f_2 uses the original glued format "(f_2>=_N)"
    if list(coeffs) == ["f_2"] and coeffs["f_2"] == 1:
        op = {">=": ">=", "<=": "<=", "=": "="}[pr["rel"]]
        return f"(f_2{op}_{int(pr['rhs'])})"
    # render from the coefficients (canonical variable names) rather than a stored
    # text, so e.g. a big_faces premise shows as "sum_pk_after_p6 <= 5"
    return f"({_render_ineq_text(pr['coeffs'], pr['rel'], int(pr['rhs']))})"


def _old_conclusion(conclusion: dict) -> str:
    coeffs = _merge_tail_display(conclusion["coeffs"])
    a = Fraction(coeffs["p_6"])
    rhs = Fraction(conclusion["rhs"])
    # p6 >= Σ (-c_v/a)·x_v + rhs/a   (p_6 isolated, coeff 1, a > 0)
    terms = []
    for v in DISPLAY_ORDER:
        if v in ("p_6", "f_2"):
            continue
        c = coeffs.get(v, 0)
        if c == 0:
            continue
        coef = Fraction(-c) / a
        name = _OLD_NAME.get(v, v)
        terms.append(name if coef == 1 else f"({_old_num(coef)} * {name})")
    const = rhs / a
    if terms:
        acc = terms[0]
        for t in terms[1:]:
            acc = f"({acc} + {t})"
        if const != 0:
            acc = f"({acc} + {_old_num(const)})"
    else:
        acc = _old_num(const)
    rel = ">=" if conclusion["rel"] == ">=" else "<="
    return f"p6 {rel} ({acc})"


def formula_string(premises: list, conclusion: dict) -> str:
    conds = ["(is_simple)"] + [_old_premise(pr) for pr in premises]
    return f"if ({' and '.join(conds)}), then {_old_conclusion(conclusion)}"


def natural_language(premises: list, conclusion: dict) -> str:
    prem_txt = ", ".join(_render_ineq_text(pr["coeffs"], pr["rel"], pr["rhs"])
                         for pr in premises)
    concl = display_text(conclusion)
    intro = ("Let M be a simple 3-polytope (a simple 3-connected planar map), "
             "with p_k the number of k-gonal faces, f_2 the total number of "
             "faces, and sum_{k>=7} p_k the number of faces of size at least 7.")
    if prem_txt:
        return f"{intro} Suppose {prem_txt}. Then {concl}."
    return f"{intro} Then {concl}."


# ── markdown ────────────────────────────────────────────────────────────────
def _steps_md(steps: list, depth: int) -> list:
    lines = []
    ind = "  " * depth
    for s in steps:
        rule = s["rule"]
        if rule == "premise":
            lines.append(f"{ind}- Premise: `{s['text']}`.")
        elif rule == "assumption":
            lines.append(f"{ind}- Assumption: `{s['text']}`.")
        elif rule == "inventory":
            lines.append(f"{ind}- Inventory `{s['inventory']}`: `{s['text']}`.")
        elif rule == "conditional":
            lines.append(f"{ind}- Inventory theorem `{s['inventory']}` "
                         f"(via `linarith`): `{s['text']}`.")
        elif rule == "combination":
            lines.append(f"{ind}- Linear combination (`linarith`): `{s['text']}`.")
        elif rule == "rounding":
            lines.append(f"{ind}- Integer rounding (`omega`): `{s['text']}`.")
        elif rule == "case_split":
            lines.append(f"{ind}- Case split (`by_cases`) on "
                         f"`{s['split_var']}` at threshold {s['split_threshold']}: "
                         f"`{s['text']}`.")
            for i, cse in enumerate(s["cases"], 1):
                lines.append(f"{ind}  - **Case {i}** (`{cse['assume']}`):")
                lines += _steps_md(cse["steps"], depth + 2)
    return lines


def build_md(data: dict) -> str:
    cj = data["conjecture"]
    lines = [f"# {data['id']}", "", "## Statement", "",
             cj["natural_language"], "",
             f"**Formula.** `{cj['formula']}`", "",
             "## Proof", ""]
    lines += _steps_md(data["proof"]["steps"], 0)
    lines += ["", "## Scores", "",
              f"- IRIS: T={data['iris']['T']:.4f}, R={data['iris']['R']:.4f}, "
              f"L={data['iris']['L']:.4f}, score={data['iris']['score']:.4f}",
              f"- hardness: {data['hardness']:.4f}",
              f"- Lean: {data['lean']['status']}"]
    return "\n".join(lines) + "\n"


# ── one attempt (worker side, v0.6.4 §II) ────────────────────────────────────
def process_premise_set(rng, pool, existing_hashes, stats, seed, accept="split_needed"):
    """v0.6.5 §2 wrapper: arm the deterministic per-group work budget, then run the
    attempt.  A group that exceeds GROUP_WORK_BUDGET LP/MILP solves is discarded as
    ``too_slow`` (a reproducible cut, since the solve count is deterministic)."""
    D.work_reset(GROUP_WORK_BUDGET)
    try:
        return _process_premise_set_impl(rng, pool, existing_hashes, stats, seed, accept)
    except D.WorkBudgetExceeded:
        stats["too_slow"] += 1
        return None


def _process_premise_set_impl(rng, pool, existing_hashes, stats, seed, accept="split_needed"):
    """Worker-side work for ONE premise set: sampling, direction enumeration, proof
    reconstruction, every check, the integer counter-model gate, and scoring.

    Returns a ``proposal`` dict (everything the main process needs to judge the
    skeleton, apply the quota, number, formalise and write) or ``None`` on a
    discard (with ``stats`` updated).  The main-process–only steps — intra-run
    exact-duplicate / skeleton / quota judgement, numbering, Lean compilation and
    record writing — are NOT done here.  Raises ``AssertionError`` on a soundness
    violation or counter-model (the whole run must then stop).

    ``existing_hashes`` is the immutable pre-run snapshot (so a candidate equal to
    a pre-existing record is dropped here); intra-run duplicates are caught by the
    main process."""
    pvecs, features, pvec_vars = pool
    # §4 (v0.4): the deduction cache is reused within one attempt (many
    # candidates re-run minimisation over the same premise subsets) but cleared
    # between attempts to bound memory.
    _ctx_cache_clear()
    premises = sample_premises(rng)
    # §2 (v0.3): premises never mention p_6 (the target variable)
    premises = [pr for pr in premises if pr["coeffs"].get("p_6", 0) == 0]
    # §1: drop premises implied by another in the same group
    premises = dedup_premises(premises)
    if not premises:
        stats["empty_premises"] += 1
        return None
    # §3 (v0.4): premises with f_2 >= c (c > 28) have no pool witness; skip the
    # pool-based non-empty / attainment checks and rely on deducer + Lean.
    covered = pool_covered(premises)
    if covered and not premises_nonempty(premises, pvec_vars):
        stats["empty_premises"] += 1
        return None

    # §2 (v0.6.2): candidates from systematic direction enumeration (LP + case
    # split), not from random pairing / a saturated pool.
    candidates = enumerate_candidates(premises, stats, rng, accept)
    if not candidates:
        stats["no_p6_canonical"] += 1
        return None

    rng.shuffle(candidates)
    for conclusion0 in candidates:
        # §1 (v0.4, fast pre-filter): reject p_6 upper bounds up front.  The
        # canonical p_6 sign is fixed by the harvested direction and is preserved
        # by strengthening; a candidate whose canonical form has no f_2 term keeps
        # that sign through term-dropping too, so this never discards a would-be
        # lower bound — it just avoids the expensive path for upper bounds.
        c0_canon = canonicalize({v: Fraction(c) for v, c in conclusion0["coeffs"].items()})
        if not ALLOW_UPPER_BOUNDS and c0_canon.get("p_6", 0) < 0 \
                and conclusion0["coeffs"].get("f_2", 0) == 0:
            stats["p6_upper_bound"] += 1
            continue

        # §4 (fast pre-filter): a conclusion linearly derivable from the full
        # (deduped) premises is discarded.  Minimization only drops premises, so
        # a conclusion not linearly derivable here is not linearly derivable from
        # any minimized subset either — hence every conjecture we keep genuinely
        # needs integer rounding or a case split on its minimized premises.
        if linearly_derivable(premises, conclusion0):
            stats["linear_only"] += 1
            continue

        # §3: greedy premise minimization
        pruned = minimize_premises(premises, conclusion0)
        # §1 (v0.5): make implied-zero variables explicit, drop redundant premises,
        # then re-minimise and de-duplicate (result is equivalent on ℕ).
        pruned = simplify_premises(pruned)
        pruned = dedup_premises(pruned)
        pruned = minimize_premises(pruned, conclusion0)
        # §1/§2 (v0.7): a lemma only "helps" this direction if its lemma-aided bound
        # beats the lemma-free one; then (and only then) is the proof allowed to use
        # lemmas, and the §2 dependency check is run.  Otherwise prove lemma-free.
        vl, vb = conclusion0.get("v_int_lemma"), conclusion0.get("v_int_base")
        lemma_helps = (vb is None) or (vl is not None and vl > vb)
        # §2 (strengthen) + §3-v0.3 (drop redundant terms)
        res = strengthen_and_simplify(conclusion0, pruned, use_lemmas=lemma_helps)
        if res is None:
            # the deducer could not reconstruct a proof for a direction the LP
            # enumeration flagged as non-linear (expected not to happen).
            stats["proof_reconstruct_failed"] += 1
            continue
        conclusion, ctx_m, fact = res
        icoeffs = conclusion["coeffs"]
        ic_frac = {v: Fraction(c) for v, c in icoeffs.items()}

        # p_6 must survive in the canonical form (f_2 eliminated)
        canon_c = canonicalize(ic_frac)
        canon_prim = D._primitive(canon_c, Fraction(-conclusion["rhs"]))
        canon_p6 = canon_c.get("p_6", 0)
        if canon_p6 == 0:
            stats["no_p6_canonical"] += 1
            continue
        # §1 (v0.4): keep only lower bounds on p_6 (canonical p_6 coeff > 0)
        if canon_p6 < 0 and not ALLOW_UPPER_BOUNDS:
            stats["p6_upper_bound"] += 1
            continue
        # §2.5 (v0.6.3): the v0.2 "minimal equivalent form must contain p_6" check
        # is removed — it only existed to cope with f_2 in the conclusion, which is
        # now forbidden (§2).  The canonical p_6 check above is kept.

        # §2 (v0.4): p_6 must be essential — if, after removing a*p_6 from the
        # canonical LHS, the remainder L' >= c is still provable, then p_6 was
        # only padded in via p_6 >= 0.  Discard as p6_padding.
        cic = {v: int(x) for v, x in canon_prim[0].items()}
        crhs = int(-canon_prim[1])
        lprime = {v: x for v, x in cic.items() if v != "p_6"}
        if not lprime:
            padding = crhs <= 0
        else:
            rp = _strongest(pruned, lprime)
            padding = rp is not None and rp[0]["rhs"] >= crhs
        if padding:
            stats["p6_padding"] += 1
            continue

        tb = traceback(ctx_m, fact)

        # §2 (v0.6.3): the display is the canonical (f_2-eliminated) form — f_2 is
        # never used to compress a conclusion.  Equal-coefficient tail faces are
        # merged to sum_pk_after_p6 at render time (§1.2).
        disp = display_conclusion({v: Fraction(x) for v, x in cic.items()}, crhs)

        # §3 (v0.6.3): at most MAX_CONCLUSION_TERMS terms besides p_6 (the merged
        # big_faces expression counts as one term).
        merged = _merge_tail_display(disp["coeffs"])
        n_terms = len([v for v in merged if v != "p_6" and merged[v] != 0])
        if n_terms > MAX_CONCLUSION_TERMS:
            stats["too_many_terms"] += 1
            continue

        # not a weakening of a (remaining) premise (canonical)
        if _weakens_premise(cic, crhs, pruned):
            stats["premise_weakening"] += 1
            continue

        # §4 (v0.1): must still need integer rounding / case split
        if linearly_derivable(pruned, conclusion):
            stats["linear_only"] += 1
            continue

        # derivation-step floor
        if _count_derivation_steps(tb) < 2:
            stats["too_shallow"] += 1
            continue

        # §3 (v0.4): attainment.  For pool-covered premises require IRIS T > 0;
        # for out-of-pool premises (f_2 >= c, c > 28) skip the check, mark unknown.
        if covered:
            iris = IRIS.iris_score(pruned, disp, features)
            if REQUIRE_ATTAINED and iris["touch_size"] == 0:
                stats["not_attained"] += 1
                continue
            attained = "yes"
        else:
            iris = {"T": 0.0, "R": 0.0, "L": 0.0, "score": 0.0}
            attained = "unknown"
            stats["skipped_pool_checks"] += 1

        touch_val = iris["touch_size"] if attained == "yes" else None
        hard = HARD.hardness(tb, pruned, disp)

        # §2 (v0.6.1): arithmetic sharpness — is c the integer minimum of the
        # conclusion LHS over premises + Inventory?
        amin = arith_min(pruned, disp)
        arith_sharp = (amin is not None and amin == int(disp["rhs"]))

        # exact-duplicate dedup against the PRE-RUN snapshot (intra-run duplicates
        # are caught by the main process, which owns the evolving record state).
        h = conjecture_hash(pruned, conclusion)
        if h in existing_hashes:
            stats["premise_minimized_duplicate" if not pruned else "duplicate"] += 1
            continue

        # metrics for the main-process skeleton judgement (not judged here).
        skel = conjecture_skeleton(pruned, disp)
        new_metrics = {"attained": attained, "touch": touch_val,
                       "arith_sharp": arith_sharp, "hardness": hard}

        # exact re-check + soundness on the real pool
        ok, msg = recheck(ctx_m, fact, pruned)
        if not ok:
            stats["recheck_failed"] += 1
            continue
        soundness_check(pruned, disp, pvecs, pvec_vars)

        # §3 (v0.5): integer counter-model gate — the conclusion MUST be a logical
        # consequence of the premises + Inventory.  If an integer counter-model
        # exists the conjecture is not Inventory-derivable: a pipeline bug.
        cm = counter_model(pruned, disp)
        if cm is not None:
            raise AssertionError(
                "COUNTER-MODEL: conclusion not derivable from Inventory.\n"
                f"  premises  : {[pr.get('text') for pr in pruned]}\n"
                f"  conclusion: {display_text(disp)}\n"
                f"  integer counter-model: {cm}\n"
                f"  proof steps: {[ (s['rule'], s['text']) for s in tb ]}")

        # §1 (v0.6.7): cost-bounded re-proving — lowest-cost proof of the SAME
        # conclusion (lemmas available only if they help this direction, §2 v0.7).
        proof_cost_initial = HARD.proof_difficulty(tb)
        tb, ctx_m, fact, proof_cost, shorten_rounds = shorten_proof(
            pruned, conclusion, tb, ctx_m, fact, proof_cost_initial,
            use_lemmas=lemma_helps)

        # §2 (v0.7): which library lemmas does the (shortest) proof use, and are they
        # essential?  Only run the (expensive) full lemma-free re-proof when the
        # lemma-aided bound beat the base bound (lemma_helps); otherwise it is lemma 0.
        lemma_cnums = sorted(F._lemma_cnums_in(tb))
        if lemma_helps and lemma_cnums:
            stats["lemma_bound_helped"] += 1
            free = shortest_lemma_free(pruned, conclusion)   # §2.2 full no-lemma reprove
            if free is not None:
                ctx_m, fact, tb, proof_cost = free
                lemma_cnums = []
                stats["lemma_dropped_dependency"] += 1        # reproved without lemmas

        # §3.1/§4.1: generation and expanded cost from the lemmas actually depended on.
        if lemma_cnums:
            generation = 1 + max(_W_LEMMA_META[c]["generation"] for c in lemma_cnums)
            proof_cost_expanded = proof_cost + sum(
                _W_LEMMA_META[c]["proof_cost_expanded"] for c in lemma_cnums)
        else:
            generation = 0
            proof_cost_expanded = proof_cost

        # §4.2: hardness = expanded proof cost / statement length (raw value).
        sl = HARD.statement_length(pruned, disp)
        hard = (proof_cost_expanded / sl) if sl else 0.0
        new_metrics = {"attained": attained, "touch": touch_val,
                       "arith_sharp": arith_sharp, "hardness": hard}
        lemma_refs = [f"C{c}" for c in lemma_cnums]

        all_inv = set()
        _used_inventory(tb, all_inv)
        inv_theorems = sorted(all_inv & INVENTORY_THEOREMS)
        lemmas_used = sorted(all_inv - INVENTORY_THEOREMS)   # HexLemmas lemmas (proof.*)

        # deterministic fids (§4) so the record is independent of the cache
        renumber_steps(tb)

        # §2 (v0.6.2): deductive-depth label — enumeration-time LP prediction only.
        depth_type = classify_depth(pruned, cic)
        # §IV (v0.6.4): the direction-level filter in enumerate_candidates classifies
        # the raw direction; after strengthening/canonicalisation the final label can
        # (rarely) differ.  Keep each phase pure: accept only the requested depth.
        if depth_type != accept:
            stats["depth_mismatch"] += 1
            continue

        # proof-structure stats from the FINAL (shortest) proof (v0.6.7: no tiers)
        proof_stats = HARD.proof_structure_stats(tb)

        return {
            "seed": seed,
            "premises": pruned,
            "disp": disp,
            "conclusion": conclusion,
            "tb": tb,
            "inv_theorems": inv_theorems,
            "lemmas_used": lemmas_used,
            "iris": {k: iris[k] for k in ("T", "R", "L", "score")},
            "attained": attained,
            "touch": touch_val,
            "arith_sharp": arith_sharp,
            "arith_min": amin,
            "hardness": hard,
            "depth_type": depth_type,
            "proof_stats": proof_stats,
            "proof_cost_initial": proof_cost_initial,
            "proof_cost": proof_cost,
            "proof_cost_expanded": proof_cost_expanded,
            "shorten_rounds": shorten_rounds,
            "generation": generation,
            "lemma_refs": lemma_refs,
            "hash": h,
            "skeleton": skel,
            "metrics": new_metrics,
        }

    return None


# ── record assembly (main side, v0.6.4 §II) ──────────────────────────────────
def assemble_data(proposal: dict, target: str, supersedes: list) -> dict:
    """Build the record ``data`` dict from a worker proposal (main process)."""
    pruned, disp = proposal["premises"], proposal["disp"]
    return {
        "id": target,
        "created_at": datetime.now(timezone.utc).isoformat(),
        "generator": {"version": GENERATOR_VERSION, "seed": proposal["seed"]},
        "conjecture": {
            "formula": formula_string(pruned, disp),
            "premises": [{"text": pr.get("text", ""),
                          "coeffs": {k: int(v) for k, v in pr["coeffs"].items()},
                          "rel": pr["rel"], "rhs": int(pr["rhs"])}
                         for pr in pruned],
            "conclusion": {
                "text": display_text(disp),
                "coeffs": {k: int(v) for k, v in disp["coeffs"].items()},
                "rel": disp["rel"], "rhs": int(disp["rhs"])},
            "natural_language": natural_language(pruned, disp),
        },
        "proof": {"inventory_used": proposal["inv_theorems"],
                  "lemmas_used": proposal["lemmas_used"],
                  "steps": proposal["tb"]},
        "iris": proposal["iris"],
        "attained": proposal["attained"],
        "touch": proposal["touch"],
        "arith_sharp": proposal["arith_sharp"],
        "arith_min": proposal["arith_min"],
        "depth_type": proposal["depth_type"],
        "proof_stats": proposal["proof_stats"],
        "proof_cost_initial": proposal["proof_cost_initial"],
        "proof_cost": proposal["proof_cost"],
        "proof_cost_expanded": proposal["proof_cost_expanded"],
        "shorten_rounds": proposal["shorten_rounds"],
        "generation": proposal["generation"],
        "lemmas_used": proposal["lemma_refs"],       # v0.7 §3: library-lemma C-numbers
        "supersedes": supersedes,
        "hardness": proposal["hardness"],
        "lean": {"theorem_name": target, "status": "compiled"},
    }


# ── multiprocessing worker plumbing (v0.6.4 §II) ──────────────────────────────
# Set in the parent before the Pool is forked so each worker inherits the loaded
# pool (copy-on-write) rather than receiving it pickled per task.
_W_POOL = None
_W_HASHES = None
_W_BASE_SEED = None


_W_LEMMA_META = {}        # cnum -> {"generation", "proof_cost_expanded"} (v0.7)


def set_worker_globals(pool, existing_hashes_snapshot, base_seed,
                       lemmas=None, lemma_meta=None):
    global _W_POOL, _W_HASHES, _W_BASE_SEED, _W_LEMMA_META
    _W_POOL = pool
    _W_HASHES = existing_hashes_snapshot
    _W_BASE_SEED = base_seed
    _W_LEMMA_META = lemma_meta or {}
    D.set_lemmas(lemmas or {})          # workers (forked after this) inherit the library


def seed_for(idx: int) -> int:
    """Deterministic per-premise-set seed from the base seed and the index (§II.2)."""
    return _W_BASE_SEED * 1_000_003 + idx


def worker(idx: int, accept: str = "split_needed"):
    """Top-level (picklable) worker entry.  Returns a tuple whose first element is
    one of ``"ok"`` / ``"soundness"`` describing the outcome.  ``accept`` selects the
    depth_type this call produces (``"split_needed"`` for the main phase,
    ``"rounding_only"`` for the supplement phase)."""
    import time as _t
    _ctx_cache_clear()
    seed = seed_for(idx)
    rng = random.Random(seed)
    local_stats = defaultdict(int)
    t0 = _t.time()
    try:
        prop = process_premise_set(rng, _W_POOL, _W_HASHES, local_stats, seed, accept)
    except AssertionError as exc:
        return ("soundness", idx, str(exc), dict(local_stats), _t.time() - t0)
    return ("ok", idx, prop, dict(local_stats), _t.time() - t0)


# ── atomic record writing ────────────────────────────────────────────────────
def write_record(data: dict, lean_src: str):
    """Write to a temp dir first, then rename to C{n}/ atomically."""
    name = data["id"]
    RECORD.mkdir(exist_ok=True)
    tmp = RECORD / f".{name}.tmp"
    if tmp.exists():
        shutil.rmtree(tmp)
    tmp.mkdir(parents=True)
    (tmp / f"{name}.json").write_text(json.dumps(data, indent=2, ensure_ascii=False))
    (tmp / f"{name}.md").write_text(build_md(data))
    (tmp / f"{name}.lean").write_text(lean_src)
    final = RECORD / name
    if final.exists():
        shutil.rmtree(final)
    os.replace(tmp, final)
    # the compiled copy lives only in the record; remove the working file that
    # the formalizer left inside the Lean project
    lean_working = F.LEAN_DIR / f"{name}.lean"
    if lean_working.exists():
        lean_working.unlink()
