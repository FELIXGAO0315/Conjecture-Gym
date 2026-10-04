"""Forward deduction engine over the closed axiom base in :mod:`inventory`.

Three inference actions (each with its Lean tactic counterpart):

    LINEAR_COMBINATION  ->  linarith    (non-negative combination of facts)
    INTEGER_ROUNDING    ->  omega       (floor an integer-coefficient bound)
    CASE_SPLIT          ->  by_cases    (branch on a threshold, merge results)

A *fact* is an integer/rational linear form that is asserted ``>= 0`` or
``== 0``.  All arithmetic used to decide truth is exact (:class:`fractions.Fraction`);
floating point is used only inside :func:`scipy.optimize.linprog` to *discover*
which facts support a bound -- the multipliers are then re-solved exactly and
re-verified before any fact enters the pool.

The engine never reads ``data/`` and never writes files.
"""

from __future__ import annotations

import itertools
from dataclasses import dataclass, field
from fractions import Fraction
from math import floor, gcd
from typing import Optional

import numpy as np
from scipy.optimize import linprog

from . import inventory
from .inventory import ALL_VARS, PROP_VARS

# ── deterministic per-group work budget (v0.6.5 §2) ─────────────────────────
# A group's cost is measured by the number of LP/MILP solves it triggers (a
# deterministic count, unlike wall-clock), accumulated across the deducer and the
# generator.  ``WORK["budget"]`` is set per premise set by the generator; when the
# count exceeds it, ``work_tick`` raises ``WorkBudgetExceeded`` and the whole group
# is discarded (``too_slow``).  ``budget=None`` disables the cap (counts only).
WORK = {"n": 0, "budget": None}


class WorkBudgetExceeded(Exception):
    """Raised by ``work_tick`` when a premise set exceeds ``WORK['budget']``."""


def work_reset(budget):
    WORK["n"] = 0
    WORK["budget"] = budget


def work_tick(k: int = 1):
    """Count ``k`` solver calls; raise if over the per-group budget (if set)."""
    WORK["n"] += k
    if WORK["budget"] is not None and WORK["n"] > WORK["budget"]:
        raise WorkBudgetExceeded(WORK["n"])

# ── Inference actions and their Lean tactics ────────────────────────────────
ACTION_LINEAR_COMBINATION = "linear_combination"  # Lean tactic: linarith
ACTION_INTEGER_ROUNDING = "integer_rounding"      # Lean tactic: omega
ACTION_CASE_SPLIT = "case_split"                  # Lean tactic: by_cases

ACTION_TACTIC = {
    ACTION_LINEAR_COMBINATION: "linarith",
    ACTION_INTEGER_ROUNDING: "omega",
    ACTION_CASE_SPLIT: "by_cases",
}

_TOL = 1e-7


# ════════════════════════════════════════════════════════════════════════════
# Linear-form helpers (coeffs is a dict var -> Fraction; const is a Fraction)
# ════════════════════════════════════════════════════════════════════════════
def _clean(coeffs: dict) -> dict:
    return {v: Fraction(c) for v, c in coeffs.items() if Fraction(c) != 0}


def _add(a: dict, b: dict, sb: Fraction = Fraction(1)) -> dict:
    out = dict(a)
    for v, c in b.items():
        out[v] = out.get(v, Fraction(0)) + sb * c
    return _clean(out)


def _scale(a: dict, s: Fraction) -> dict:
    return _clean({v: c * s for v, c in a.items()})


def _lcm(a: int, b: int) -> int:
    return a * b // gcd(a, b) if a and b else max(a, b)


def _primitive(coeffs: dict, const: Fraction):
    """Scale ``(coeffs, const)`` by a positive rational so the *variable*
    coefficients become coprime integers.  Returns ``(int_coeffs, new_const)``.
    ``None`` if all variable coefficients are zero."""
    if not coeffs:
        return None
    dens = [c.denominator for c in coeffs.values()]
    L = 1
    for d in dens:
        L = _lcm(L, d)
    ints = {v: int(c * L) for v, c in coeffs.items()}
    g = 0
    for c in ints.values():
        g = gcd(g, abs(c))
    if g == 0:
        return None
    s = Fraction(L, g)          # positive scale factor
    new_coeffs = {v: Fraction(c * L // g) for v, c in coeffs.items()}
    return new_coeffs, const * s


# ════════════════════════════════════════════════════════════════════════════
# Fact
# ════════════════════════════════════════════════════════════════════════════
@dataclass
class Fact:
    """A linear form asserted ``form rel 0`` where ``form = sum coeffs*var + const``."""
    fid: int
    coeffs: dict           # var -> Fraction
    const: Fraction
    rel: str               # ">=" or "=="
    rule: str              # premise|inventory|conditional|combination|rounding|
                           # case_split|assumption
    inv_name: Optional[str] = None
    deps: list = field(default_factory=list)      # dependency fact ids
    mults: list = field(default_factory=list)     # parallel multipliers (combination)
    split_var: Optional[str] = None               # case_split (label)
    split_threshold: Optional[int] = None
    split_coeffs: Optional[dict] = None           # case_split linear expression
    split_kind: Optional[str] = None              # "conditional" | "bnb" (v0.6.6)
    branches: list = field(default_factory=list)  # case_split: [(label, Context, fid)]
    lemma_cnum: Optional[int] = None              # v0.7: C-number of the lemma applied
    lemma_premises: Optional[list] = None         # v0.7: the lemma's premises (for Lean)
    note: str = ""

    def value_at(self, vals: dict) -> Fraction:
        s = Fraction(self.const)
        for v, c in self.coeffs.items():
            s += c * vals.get(v, 0)
        return s

    def holds_at(self, vals: dict) -> bool:
        val = self.value_at(vals)
        return val == 0 if self.rel == "==" else val >= 0

    def lhs_key(self):
        """Canonical key of the variable part (for de-duplication)."""
        prim = _primitive(self.coeffs, self.const)
        if prim is None:
            return None
        ic, _ = prim
        if self.rel == "==":
            # canonical sign: first nonzero coeff positive
            for v in ALL_VARS:
                if ic.get(v, 0) != 0:
                    if ic[v] < 0:
                        ic = {k: -x for k, x in ic.items()}
                    break
        return tuple(sorted((v, int(c)) for v, c in ic.items()))

    def bound(self) -> Fraction:
        """Lower bound on the primitive LHS (``prim_coeffs . x >= bound``)."""
        prim = _primitive(self.coeffs, self.const)
        _, nc = prim
        return -nc


def _fmt_form(coeffs: dict, const: Fraction) -> str:
    parts = []
    for v in ALL_VARS:
        c = coeffs.get(v, 0)
        if c == 0:
            continue
        cc = c if c.denominator != 1 else c.numerator
        parts.append(f"{cc}*{v}")
    if const != 0:
        cc = const if const.denominator != 1 else const.numerator
        parts.append(str(cc))
    return " + ".join(parts) if parts else "0"


def fact_text(f: Fact) -> str:
    return f"{_fmt_form(f.coeffs, f.const)} {f.rel} 0"


# ════════════════════════════════════════════════════════════════════════════
# Building facts from inventory / premises
# ════════════════════════════════════════════════════════════════════════════
def _conc_to_form(conc: dict):
    """Inventory conclusion {coeffs, rel, rhs} -> (coeffs, const, rel) as form rel 0."""
    coeffs = _clean(conc["coeffs"])
    rhs = Fraction(conc["rhs"])
    rel = conc["rel"]
    if rel == "=":
        return coeffs, -rhs, "=="
    if rel == ">=":
        return coeffs, -rhs, ">="
    if rel == "<=":
        # (sum) <= rhs  ->  rhs - sum >= 0
        return _scale(coeffs, Fraction(-1)), rhs, ">="
    raise ValueError(rel)


# ════════════════════════════════════════════════════════════════════════════
# Exact linear solve (Fraction gaussian elimination)
# ════════════════════════════════════════════════════════════════════════════
def _solve_exact(A: list, b: list):
    """Solve A x = b exactly (rows may exceed cols).  Returns a particular
    solution (free variables set to 0) or ``None`` if inconsistent."""
    rows = len(A)
    cols = len(A[0]) if rows else 0
    M = [[Fraction(x) for x in A[i]] + [Fraction(b[i])] for i in range(rows)]
    pivots = []
    r = 0
    for c in range(cols):
        piv = next((i for i in range(r, rows) if M[i][c] != 0), None)
        if piv is None:
            continue
        M[r], M[piv] = M[piv], M[r]
        inv = M[r][c]
        M[r] = [x / inv for x in M[r]]
        for i in range(rows):
            if i != r and M[i][c] != 0:
                f = M[i][c]
                M[i] = [M[i][j] - f * M[r][j] for j in range(cols + 1)]
        pivots.append((r, c))
        r += 1
        if r == rows:
            break
    # consistency of zero rows
    for i in range(rows):
        if all(M[i][j] == 0 for j in range(cols)) and M[i][cols] != 0:
            return None
    x = [Fraction(0)] * cols
    for (ri, ci) in pivots:
        x[ci] = M[ri][cols]
    return x


# ════════════════════════════════════════════════════════════════════════════
# Deduction context (one node of the case-split tree)
# ════════════════════════════════════════════════════════════════════════════
# Directed objectives explored every round.  Each is a coefficient dict; the
# engine finds the tightest provable lower bound ``dir . x >= b`` on the pool.
_TAIL_COUNT = {v: 1 for v in inventory.TAIL_COUNT_VARS}   # p_7..p_10 + tail


def _base_directions() -> list:
    dirs = []
    for v in PROP_VARS:
        dirs.append({v: 1})
    combos = [
        dict({"p_6": 2}, **_TAIL_COUNT),          # 2 p_6 + (tail count)
        {"p_6": 3},
        {"p_6": 1, "p_5": -1},
        {"p_6": 1, "p_5": 1},
        {"p_6": 1, "p_4": -1},
        {"p_6": 1, "p_3": -1},
        dict({"p_6": 1}, **_TAIL_COUNT),
        {"p_6": 2, "p_5": 1},
        {"p_6": 1, "f_2": -1},
        {"p_3": 1, "p_4": 1, "p_5": 1},
        {"p_4": 1, "p_5": 1},
    ]
    dirs.extend(combos)
    # also seek upper bounds (max) by minimising the negation
    dirs.extend([{v: -c for v, c in d.items()} for d in list(dirs)])
    return dirs


BASE_DIRECTIONS = _base_directions()

# Case-split expressions and their thresholds (conditional trigger c and c+1).
# Each spec is (label, coeff-dict, thresholds) — the split is on a linear form.
SPLIT_SPECS = [
    ("tail_count", dict(_TAIL_COUNT), [3, 4]),   # Barnette trigger
    ("f_2", {"f_2": 1}, [7, 8]),                 # Jučovič trigger
]

# v0.6.6 §1: branch-and-bound case splits.  When the LP optimum for a direction we
# are trying to bound lands on a FRACTIONAL value of one of these variables, split
# on ``var <= floor(x*)`` vs ``var >= ceil(x*)`` so the proof depth can grow beyond
# what the fixed conditional-theorem splits (tail_count, f_2) allow.
BNB_VARS = ["p_3", "p_4", "p_5", "p_6", "sum_pk_after_p6", "f_2"]
_BNB_FRAC_TOL = 1e-6


def _bnb_pick_var(xstar: dict):
    """Deterministically pick the B&B variable: the one in ``BNB_VARS`` whose LP
    value has fractional part closest to 0.5 (ties broken by the fixed BNB_VARS
    order).  Returns ``(var, floor(x*))`` or ``None`` if all are (near-)integral."""
    best = None
    for v in BNB_VARS:
        x = float(xstar.get(v, 0.0))
        frac = x - floor(x)
        if frac <= _BNB_FRAC_TOL or frac >= 1.0 - _BNB_FRAC_TOL:
            continue                              # (near-)integral: nothing to split
        dist = abs(frac - 0.5)
        if best is None or dist < best[0] - 1e-12:
            best = (dist, v, floor(x))
    return (best[1], best[2]) if best is not None else None

# v0.7 §2: lemma library — proved conjectures used as extra conditional theorems.
# ``LEMMAS`` maps C-number -> {"premises": [{coeffs,rel,rhs}], "coeffs": {var:Fraction},
# "const": Fraction, "rel": ">="} where (coeffs,const,rel) is the conclusion as a Fact
# form (coeffs·x + const >= 0).  Set per run by the generator; empty by default.
LEMMAS: dict = {}


def set_lemmas(lemmas: dict):
    global LEMMAS
    LEMMAS = lemmas


DEFAULT_MAX_ROUNDS = 8
# v0.6.5 §4: case-split nesting raised 2 → 3 (the 3rd level reuses the same
# thresholds: f_2 ∈ {7,8}, big-face total ∈ {3,4}).  The per-group work budget
# (§2) keeps the deeper, exponentially larger split trees in check.
DEFAULT_SPLIT_DEPTH = 3
# v0.6.2: candidates come from systematic direction enumeration (generator), not
# from pairwise Fourier–Motzkin, so pairwise is off by default.  The facts the
# proofs use are supplied by the LP directed bounds.
USE_PAIRWISE = False


class Context:
    """A pool of facts closed under the inference actions, plus (recursively)
    the child contexts created by case splits."""

    _counter = itertools.count(1)

    def __init__(self, premises=None, assumptions=None, depth=DEFAULT_SPLIT_DEPTH,
                 max_rounds=DEFAULT_MAX_ROUNDS, extra_directions=None, label="",
                 use_conditional_split=True, use_bnb=True, use_lemmas=True):
        self.facts: list = []
        self._by_lhs: dict = {}     # lhs_key -> Fact (strongest)
        self._markers: set = set()  # triggered-conditional / attempted-split keys
        self.depth = depth
        self.max_rounds = max_rounds
        self.directions = list(BASE_DIRECTIONS) + list(extra_directions or [])
        self.label = label
        # v0.6.7 §1: restrict the split kinds (used by cost-bounded re-proving to
        # search for a cheaper proof under different method restrictions).
        self.use_conditional_split = use_conditional_split
        self.use_bnb = use_bnb
        self.use_lemmas = use_lemmas            # v0.7: may apply library lemmas
        self.children: dict = {}    # (var, c, "ge"/"le") -> Context

        # 1. Unconditional inventory facts.
        for e in inventory.INVENTORY:
            if e["kind"] in ("equality", "inequality"):
                coeffs, const, rel = _conc_to_form(e["conclusion"])
                self._add(Fact(next(self._counter), coeffs, const, rel,
                               rule="inventory", inv_name=e["name"]))
        # 2. Premises supplied by the generator.
        for pr in (premises or []):
            coeffs, const, rel = _conc_to_form(pr)
            self._add(Fact(next(self._counter), coeffs, const, rel,
                           rule="premise", note=pr.get("text", "")))
        # 3. Branch assumptions (from an enclosing case split).
        for asm in (assumptions or []):
            coeffs, const, rel = _conc_to_form(asm["cond"])
            self._add(Fact(next(self._counter), coeffs, const, rel,
                           rule="assumption", note=asm.get("text", "")))

    # ── pool management ─────────────────────────────────────────────────────
    def _add(self, fact: Fact) -> bool:
        """Insert ``fact`` if it is new or strictly stronger.  Returns True if
        the pool changed."""
        key = fact.lhs_key()
        if key is None:
            return False
        if fact.rel == "==":
            ekey = ("==", key)
            if ekey in self._by_lhs:
                return False
            self._by_lhs[ekey] = fact
            self.facts.append(fact)
            return True
        # inequality: keep strongest lower bound for this LHS direction
        ikey = (">=", key)
        prev = self._by_lhs.get(ikey)
        if prev is not None and fact.bound() <= prev.bound():
            return False
        self._by_lhs[ikey] = fact
        self.facts.append(fact)
        return True

    def _active_ineqs_eqs(self):
        ineqs = [f for f in self._by_lhs.values() if f.rel == ">="]
        eqs = [f for f in self._by_lhs.values() if f.rel == "=="]
        return ineqs, eqs

    # ── action: trigger conditional theorems ────────────────────────────────
    def _trigger_conditionals(self) -> bool:
        changed = False
        for e in inventory.CONDITIONAL_THEOREMS:
            key = ("triggered", e["name"])
            if key in self._markers:
                continue
            hyp = e["hypothesis"]                 # (sum) >= rhs
            hcoeffs, hconst, _ = _conc_to_form(hyp)   # form >= 0
            trig = self._entails(hcoeffs, hconst)
            if trig is None:
                continue
            coeffs, const, rel = _conc_to_form(e["conclusion"])
            f = Fact(next(self._counter), coeffs, const, rel,
                     rule="conditional", inv_name=e["name"], deps=[trig.fid])
            self._markers.add(key)
            if self._add(f):
                changed = True
        return changed

    # ── action: trigger library lemmas (v0.7 §2) ─────────────────────────────
    def _premise_entails(self, pr):
        """Return a pool Fact entailing premise ``pr`` ({coeffs, rel, rhs}), else None."""
        cf = {v: Fraction(c) for v, c in pr["coeffs"].items()}
        rhs = Fraction(pr["rhs"])
        rel = pr["rel"]
        if rel == ">=":
            return self._entails(cf, -rhs)
        if rel == "<=":
            return self._entails({v: -c for v, c in cf.items()}, rhs)
        if rel in ("=", "=="):
            ge = self._entails(cf, -rhs)
            le = self._entails({v: -c for v, c in cf.items()}, rhs)
            return ge if (ge is not None and le is not None) else None
        return None

    def _trigger_lemmas(self) -> bool:
        if not self.use_lemmas or not LEMMAS:
            return False
        changed = False
        for cnum in sorted(LEMMAS):                 # deterministic order
            key = ("lemma", cnum)
            if key in self._markers:
                continue
            lem = LEMMAS[cnum]
            deps, ok = [], True
            for pr in lem["premises"]:              # all premises must be entailed
                dep = self._premise_entails(pr)
                if dep is None:
                    ok = False
                    break
                deps.append(dep.fid)
            if not ok:
                continue
            self._markers.add(key)
            f = Fact(next(self._counter), dict(lem["coeffs"]), lem["const"], lem["rel"],
                     rule="lemma", lemma_cnum=cnum, lemma_premises=lem["premises"], deps=deps)
            if self._add(f):
                changed = True
        return changed

    def _entails(self, coeffs: dict, const: Fraction):
        """Return a pool fact proving ``coeffs . x + const >= 0`` (a >= fact with
        the same LHS and a bound at least as strong), else None."""
        prim = _primitive(coeffs, const)
        if prim is None:
            return None
        ic, nc = prim
        need = -nc
        for v in ALL_VARS:                        # sign-normalise for lookup
            pass
        key = tuple(sorted((v, int(c)) for v, c in ic.items()))
        f = self._by_lhs.get((">=", key))
        if f is not None and f.bound() >= need:
            return f
        # an equality with the same LHS also entails any bound it meets
        for eq in [x for x in self._by_lhs.values() if getattr(x, "rel", None) == "=="]:
            eprim = _primitive(eq.coeffs, eq.const)
            if eprim is None:
                continue
            eic, enc = eprim
            ekey = tuple(sorted((v, int(c)) for v, c in eic.items()))
            if ekey == key and -enc >= need:
                return eq
        return None

    # ── action: directed bounds via LP + exact certificate ──────────────────
    def _directed_bounds(self) -> bool:
        changed = False
        ineqs, eqs = self._active_ineqs_eqs()
        idx = {v: i for i, v in enumerate(ALL_VARS)}
        n = len(ALL_VARS)
        A_ub, b_ub = [], []
        for f in ineqs:                           # coeffs.x + const >= 0  ->  -coeffs.x <= const
            row = [0.0] * n
            for v, c in f.coeffs.items():
                row[idx[v]] = -float(c)
            A_ub.append(row)
            b_ub.append(float(f.const))
        A_eq, b_eq = [], []
        for f in eqs:                             # coeffs.x + const == 0  ->  coeffs.x == -const
            row = [0.0] * n
            for v, c in f.coeffs.items():
                row[idx[v]] = float(c)
            A_eq.append(row)
            b_eq.append(-float(f.const))

        for direction in self.directions:
            c = [0.0] * n
            for v, coef in direction.items():
                c[idx[v]] = float(coef)
            work_tick()                           # v0.6.5 §2: count this LP solve
            try:
                res = linprog(c, A_ub=A_ub or None, b_ub=b_ub or None,
                              A_eq=A_eq or None, b_eq=b_eq or None,
                              bounds=[(None, None)] * n, method="highs")
            except Exception:
                continue
            if not res.success or not np.isfinite(res.fun):
                continue
            # support facts from nonzero duals
            support = []
            if A_ub:
                marg = np.atleast_1d(res.ineqlin.marginals)
                for i, m in enumerate(marg):
                    if abs(m) > _TOL:
                        support.append(("ineq", ineqs[i]))
            if A_eq:
                marg = np.atleast_1d(res.eqlin.marginals)
                for j, m in enumerate(marg):
                    if abs(m) > _TOL:
                        support.append(("eq", eqs[j]))
            if not support:
                continue
            cert = self._exact_certificate(direction, support)
            if cert is None:
                continue
            mults, const_K = cert
            coeffs = {v: Fraction(coef) for v, coef in direction.items()}
            rel = "==" if all(t == "eq" for t, _ in support) else ">="
            f = Fact(next(self._counter), _clean(coeffs), const_K, rel,
                     rule="combination",
                     deps=[fc.fid for _, fc in support],
                     mults=mults)
            if self._add(f):
                changed = True
        return changed

    def _exact_certificate(self, direction: dict, support: list):
        """Solve for exact multipliers so ``sum lambda_i form_i`` has variable
        part equal to ``direction``.  Returns ``(mults, K)`` with the resulting
        constant, or ``None`` if no valid (sign-correct) certificate exists."""
        facts = [fc for _, fc in support]
        kinds = [k for k, _ in support]
        A = []                                    # one row per variable
        b = []
        for v in ALL_VARS:
            A.append([float(fc.coeffs.get(v, 0)) for fc in facts])  # placeholder
            b.append(direction.get(v, 0))
        # rebuild A with exact Fractions
        A = [[fc.coeffs.get(v, Fraction(0)) for fc in facts] for v in ALL_VARS]
        b = [Fraction(direction.get(v, 0)) for v in ALL_VARS]
        sol = _solve_exact(A, b)
        if sol is None:
            return None
        # verify sign constraints (>= facts need lambda >= 0)
        for lam, kind in zip(sol, kinds):
            if kind == "ineq" and lam < 0:
                return None
        # verify the combination reproduces the direction exactly
        combo = {}
        K = Fraction(0)
        for lam, fc in zip(sol, facts):
            combo = _add(combo, fc.coeffs, lam)
            K += lam * fc.const
        for v in ALL_VARS:
            if combo.get(v, Fraction(0)) != Fraction(direction.get(v, 0)):
                return None
        return list(sol), K

    # ── action: integer rounding ────────────────────────────────────────────
    def _round(self) -> bool:
        changed = False
        for f in list(self._by_lhs.values()):
            if getattr(f, "rel", None) != ">=":
                continue
            if f.rule == "rounding":
                continue
            prim = _primitive(f.coeffs, f.const)
            if prim is None:
                continue
            ic, nc = prim
            if nc.denominator == 1:
                continue                          # already integral -> nothing gained
            floored = Fraction(floor(nc))
            nf = Fact(next(self._counter), dict(ic), floored, ">=",
                      rule="rounding", deps=[f.fid])
            if self._add(nf):
                changed = True
        return changed

    # ── one closure pass (no splitting) ─────────────────────────────────────
    def _saturate(self) -> None:
        for rnd in range(self.max_rounds):
            changed = False
            changed |= self._trigger_conditionals()
            changed |= self._trigger_lemmas()
            # bounded pairwise elimination only on the first pass (supplementary
            # to the LP-directed bounds, which are the main engine).  Skipped once
            # the pool is large: with the expanded v0.6.1 variable set it is
            # O(n²) and explodes on weak-premise pools, while the directed bounds
            # already supply the facts the proofs use.
            if rnd == 0 and USE_PAIRWISE:
                changed |= self._pairwise()
            changed |= self._directed_bounds()
            changed |= self._round()
            if not changed:
                break

    # ── action: pairwise elimination (Fourier-Motzkin, supplementary) ───────
    def _pairwise(self) -> bool:
        changed = False
        facts = [f for f in self._by_lhs.values()]
        for f1, f2 in itertools.combinations(facts, 2):
            common = set(f1.coeffs) & set(f2.coeffs)
            for v in common:
                a1, a2 = f1.coeffs.get(v, Fraction(0)), f2.coeffs.get(v, Fraction(0))
                if a1 == 0 or a2 == 0:
                    continue
                # choose non-negative multipliers that cancel v
                combos = []
                if f1.rel == ">=" and f2.rel == ">=":
                    if (a1 > 0) != (a2 > 0):      # opposite signs
                        combos.append((abs(a2), abs(a1)))
                elif f1.rel == "==" or f2.rel == "==":
                    l1 = a2 if f1.rel == "==" else abs(a2)
                    l2 = -a1 if f2.rel != "==" else -a1
                    # normalise so v cancels: l1*a1 + l2*a2 = 0
                    combos.append((a2, -a1))
                for (l1, l2) in combos:
                    if l1 == 0 and l2 == 0:
                        continue
                    # ensure sign validity for inequalities
                    if f1.rel == ">=" and l1 < 0:
                        continue
                    if f2.rel == ">=" and l2 < 0:
                        continue
                    coeffs = _add(_scale(f1.coeffs, l1), _scale(f2.coeffs, l2))
                    if v in coeffs:
                        continue
                    if not coeffs:
                        continue
                    const = l1 * f1.const + l2 * f2.const
                    rel = "==" if (f1.rel == "==" and f2.rel == "==") else ">="
                    nf = Fact(next(self._counter), coeffs, const, rel,
                              rule="combination", deps=[f1.fid, f2.fid],
                              mults=[l1, l2])
                    if self._add(nf):
                        changed = True
        return changed

    # ── branch-and-bound split selection (v0.6.6 §1) ─────────────────────────
    def _lp_vertex(self, direction: dict):
        """Solve ``min direction·x`` over the current facts; return ``(value,
        {var: x_i})`` for the optimal vertex, or ``None`` if infeasible/unbounded."""
        ineqs, eqs = self._active_ineqs_eqs()
        idx = {v: i for i, v in enumerate(ALL_VARS)}
        n = len(ALL_VARS)
        A_ub, b_ub = [], []
        for f in ineqs:
            row = [0.0] * n
            for v, c in f.coeffs.items():
                row[idx[v]] = -float(c)
            A_ub.append(row); b_ub.append(float(f.const))
        A_eq, b_eq = [], []
        for f in eqs:
            row = [0.0] * n
            for v, c in f.coeffs.items():
                row[idx[v]] = float(c)
            A_eq.append(row); b_eq.append(-float(f.const))
        c = [0.0] * n
        for v, coef in direction.items():
            c[idx[v]] = float(coef)
        work_tick()
        try:
            res = linprog(c, A_ub=A_ub or None, b_ub=b_ub or None,
                          A_eq=A_eq or None, b_eq=b_eq or None,
                          bounds=[(None, None)] * n, method="highs")
        except Exception:
            return None
        if not res.success or not np.isfinite(res.fun):
            return None
        return float(res.fun), {v: float(res.x[idx[v]]) for v in ALL_VARS}

    def _bnb_splits(self):
        """Deterministic B&B split candidates ``(var, threshold)`` from the extra
        (candidate) directions whose LP optimum is fractional in a B&B variable."""
        out, seen = [], set()
        for d in self.directions[len(BASE_DIRECTIONS):]:
            v = self._lp_vertex(d)
            if v is None:
                continue
            pick = _bnb_pick_var(v[1])
            if pick is None:
                continue
            var, fl = pick
            key = (var, fl + 1)
            if key in seen:
                continue
            seen.add(key)
            out.append(key)
        return out

    # ── case splitting ──────────────────────────────────────────────────────
    def saturate(self) -> None:
        """Full closure including case splits (conditional-theorem and branch-and-
        bound) down to ``self.depth``."""
        self._saturate()
        if self.depth <= 0:
            return
        progress = True
        while progress:
            progress = False
            if self.use_conditional_split:
                for label, coeffs, thresholds in SPLIT_SPECS:
                    for c in thresholds:
                        if self._merge_case_split(label, coeffs, c, kind="conditional"):
                            progress = True
            # v0.6.6 §1: branch-and-bound splits on fractional LP variables
            if self.use_bnb:
                for var, k in self._bnb_splits():
                    if self._merge_case_split(f"bnb:{var}", {var: Fraction(1)}, k,
                                              kind="bnb"):
                        progress = True
            if progress:
                self._saturate()

    def _decided(self, coeffs: dict, c: int) -> bool:
        """True if ``expr >= c`` or ``expr <= c-1`` is already provable."""
        ge = self._entails(dict(coeffs), Fraction(-c)) is not None
        le = self._entails({v: -x for v, x in coeffs.items()}, Fraction(c - 1)) is not None
        return ge or le

    def _merge_case_split(self, label: str, coeffs: dict, c: int,
                          kind: str = "conditional") -> bool:
        if self._decided(coeffs, c):
            return False
        key_c = tuple(sorted(coeffs.items()))
        skey = ("split", key_c, c)
        if skey in self.children:
            return False
        self._markers.add(skey)
        base_prem = [f for f in self.facts if f.rule in ("premise", "assumption")]
        etext = _fmt_form(coeffs, Fraction(0))

        def branch(cond, text):
            ctx = Context(depth=self.depth - 1, max_rounds=self.max_rounds,
                          extra_directions=self.directions[len(BASE_DIRECTIONS):],
                          label=f"{self.label}/{text}",
                          use_conditional_split=self.use_conditional_split,
                          use_bnb=self.use_bnb, use_lemmas=self.use_lemmas)
            for f in base_prem:
                ctx._add(Fact(next(ctx._counter), dict(f.coeffs), f.const, f.rel,
                              rule=f.rule, note=f.note))
            ac, aconst, arel = _conc_to_form(cond)
            ctx._add(Fact(next(ctx._counter), ac, aconst, arel,
                          rule="assumption", note=text))
            ctx.saturate()
            return ctx

        ctx_ge = branch({"coeffs": dict(coeffs), "rel": ">=", "rhs": c},
                        f"{etext} >= {c}")
        ctx_le = branch({"coeffs": dict(coeffs), "rel": "<=", "rhs": c - 1},
                        f"{etext} <= {c - 1}")
        self.children[skey] = (ctx_ge, ctx_le)

        changed = False
        ge_ineqs = {f.lhs_key(): f for f in ctx_ge._by_lhs.values() if f.rel == ">="}
        le_ineqs = {f.lhs_key(): f for f in ctx_le._by_lhs.values() if f.rel == ">="}
        for key in set(ge_ineqs) & set(le_ineqs):
            fg, fl = ge_ineqs[key], le_ineqs[key]
            merged_bound = min(fg.bound(), fl.bound())
            ic, _ = _primitive(fg.coeffs, fg.const)
            merged = Fact(next(self._counter), {v: Fraction(x) for v, x in ic.items()},
                          -merged_bound, ">=",
                          rule="case_split", split_var=label, split_threshold=c,
                          split_coeffs=dict(coeffs), split_kind=kind,
                          branches=[(f"{etext} >= {c}", ctx_ge, fg.fid),
                                    (f"{etext} <= {c - 1}", ctx_le, fl.fid)])
            if self._add(merged):
                changed = True
        return changed

    # ── queries ─────────────────────────────────────────────────────────────
    def best_bound(self, direction: dict):
        """Return the strongest pool fact whose LHS equals ``direction`` (as a
        primitive vector), or None."""
        prim = _primitive({v: Fraction(x) for v, x in direction.items()}, Fraction(0))
        if prim is None:
            return None
        ic, _ = prim
        key = tuple(sorted((v, int(x)) for v, x in ic.items()))
        return self._by_lhs.get((">=", key))

    def all_prop_facts(self):
        """All >= facts whose LHS lies entirely in the proposition variables."""
        out = []
        for f in self._by_lhs.values():
            if getattr(f, "rel", None) != ">=":
                continue
            if all(v in PROP_VARS for v in f.coeffs):
                out.append(f)
        return out


def _reconstruct_rhs(f: Fact) -> Fraction:
    return Fraction(0)


# ════════════════════════════════════════════════════════════════════════════
# Traceback: minimal ordered proof for one fact
# ════════════════════════════════════════════════════════════════════════════
def traceback(ctx: Context, fact: Fact) -> list:
    """Return an ordered, minimal list of proof steps for ``fact`` within
    ``ctx``.  Case-split steps recurse into both branch sub-proofs."""
    steps: list = []
    seen: set = set()
    fact_by_id = {f.fid: f for f in ctx.facts}

    def visit(f: Fact):
        if f.fid in seen:
            return
        seen.add(f.fid)
        if f.rule in ("premise", "assumption", "inventory"):
            pass  # leaves; still emit for premises/inventory below
        elif f.rule in ("conditional", "lemma"):
            for d in f.deps:
                if d in fact_by_id:
                    visit(fact_by_id[d])
        elif f.rule in ("combination",):
            for d in f.deps:
                if d in fact_by_id:
                    visit(fact_by_id[d])
        elif f.rule == "rounding":
            for d in f.deps:
                if d in fact_by_id:
                    visit(fact_by_id[d])
        elif f.rule == "case_split":
            pass  # branch sub-proofs handled in emit
        _emit(f)

    def _emit(f: Fact):
        step = {
            "fid": f.fid,
            "rule": f.rule,
            "text": fact_text(f),
            "coeffs": {v: str(c) for v, c in f.coeffs.items()},
            "const": str(f.const),
            "rel": f.rel,
        }
        if f.rule == "inventory":
            step["inventory"] = f.inv_name
        elif f.rule == "conditional":
            step["inventory"] = f.inv_name
            step["tactic"] = "linarith"
            step["deps"] = f.deps
        elif f.rule == "lemma":                    # v0.7 §2
            step["lemma_cnum"] = f.lemma_cnum
            step["lemma_premises"] = f.lemma_premises
            step["tactic"] = "linarith"
            step["deps"] = f.deps                  # one entailing fact fid per premise
        elif f.rule == "premise":
            step["note"] = f.note
        elif f.rule == "assumption":
            step["note"] = f.note
        elif f.rule == "combination":
            step["tactic"] = ACTION_TACTIC[ACTION_LINEAR_COMBINATION]
            step["deps"] = f.deps
            step["mults"] = [str(m) for m in f.mults]
        elif f.rule == "rounding":
            step["tactic"] = ACTION_TACTIC[ACTION_INTEGER_ROUNDING]
            step["deps"] = f.deps
        elif f.rule == "case_split":
            step["tactic"] = ACTION_TACTIC[ACTION_CASE_SPLIT]
            step["split_var"] = f.split_var
            step["split_threshold"] = f.split_threshold
            step["split_coeffs"] = {v: str(c) for v, c in (f.split_coeffs or {}).items()}
            step["split_kind"] = f.split_kind or "conditional"
            step["cases"] = []
            for (label, child, cfid) in f.branches:
                cfact = next(x for x in child.facts if x.fid == cfid)
                sub = traceback(child, cfact)
                step["cases"].append({"assume": label, "steps": sub})
        steps.append(step)

    visit(fact)
    return steps


# ════════════════════════════════════════════════════════════════════════════
# Exact re-checker (independent of the deduction that produced the proof)
# ════════════════════════════════════════════════════════════════════════════
def _inv_form(name: str):
    e = inventory.INVENTORY_BY_NAME[name]
    coeffs, const, rel = _conc_to_form(e["conclusion"])
    return coeffs, const, rel


def _dep_entails_premise(dep: Fact, pr: dict) -> bool:
    """v0.7: does already-verified fact ``dep`` entail lemma premise ``pr``
    ({coeffs, rel, rhs})?  Strict for >=/<=; lenient (same LHS) for = (Lean is the
    final arbiter for lemma applications)."""
    cf = {v: Fraction(c) for v, c in pr["coeffs"].items()}
    rhs = Fraction(pr["rhs"])
    rel = pr["rel"]
    if rel in ("=", "=="):
        pt = _primitive(cf, -rhs)
        pd = _primitive(dep.coeffs, dep.const)
        if pt is None or pd is None:
            return False
        kt = tuple(sorted(pt[0].items()))
        kd = tuple(sorted(pd[0].items()))
        kdn = tuple(sorted({v: -x for v, x in pd[0].items()}.items()))
        return kt == kd or kt == kdn
    if rel == ">=":
        tc, tk = cf, -rhs
    else:                                            # "<="
        tc, tk = {v: -c for v, c in cf.items()}, rhs
    prim_t = _primitive(tc, tk)
    prim_d = _primitive(dep.coeffs, dep.const)
    if prim_t is None or prim_d is None:
        return False
    it, nt = prim_t
    idd, nd = prim_d
    if tuple(sorted(it.items())) != tuple(sorted(idd.items())):
        return False
    return -nd >= -nt


def recheck(ctx: Context, fact: Fact, premises: list) -> tuple:
    """Re-verify a proof from scratch.  Rebuilds each step's canonical form with
    an independent elimination order and checks every inference action.
    Returns ``(ok, message)``."""
    prem_forms = []
    for pr in premises:
        c, k, r = _conc_to_form(pr)
        prem_forms.append((c, k, r))

    def same_form(c1, k1, c2, k2):
        return _clean(c1) == _clean(c2) and Fraction(k1) == Fraction(k2)

    def check(f: Fact, local_ctx: Context, local_asm: list) -> bool:
        fid_map = {x.fid: x for x in local_ctx.facts}
        if f.rule == "inventory":
            ic, ik, ir = _inv_form(f.inv_name)
            return same_form(ic, ik, f.coeffs, f.const) and ir == f.rel
        if f.rule == "premise":
            for (c, k, r) in prem_forms:
                if same_form(c, k, f.coeffs, f.const) and r == f.rel:
                    return True
            return False
        if f.rule == "assumption":
            for (c, k, r) in local_asm:
                if same_form(c, k, f.coeffs, f.const) and r == f.rel:
                    return True
            return False
        if f.rule == "conditional":
            e = inventory.INVENTORY_BY_NAME[f.inv_name]
            cc, kk, rr = _conc_to_form(e["conclusion"])
            if not (same_form(cc, kk, f.coeffs, f.const) and rr == f.rel):
                return False
            # the hypothesis must be entailed by the cited dependency
            hc, hk, _ = _conc_to_form(e["hypothesis"])
            dep = fid_map.get(f.deps[0]) if f.deps else None
            if dep is None or not check(dep, local_ctx, local_asm):
                return False
            # dep must prove hypothesis form (same LHS, bound strong enough)
            prim_h = _primitive(hc, hk)
            prim_d = _primitive(dep.coeffs, dep.const)
            if prim_h is None or prim_d is None:
                return False
            ih, nh = prim_h
            idd, nd = prim_d
            if tuple(sorted(ih.items())) != tuple(sorted(idd.items())):
                # dep may be an equality with same LHS
                return -nd >= -nh if dep.rel in (">=", "==") else False
            return -nd >= -nh
        if f.rule == "combination":
            combo = {}
            K = Fraction(0)
            for m, d in zip(f.mults, f.deps):
                dep = fid_map.get(d)
                if dep is None or not check(dep, local_ctx, local_asm):
                    return False
                if dep.rel == ">=" and Fraction(m) < 0:
                    return False
                combo = _add(combo, dep.coeffs, Fraction(m))
                K += Fraction(m) * dep.const
            return same_form(combo, K, f.coeffs, f.const)
        if f.rule == "rounding":
            dep = fid_map.get(f.deps[0])
            if dep is None or not check(dep, local_ctx, local_asm):
                return False
            prim = _primitive(dep.coeffs, dep.const)
            if prim is None:
                return False
            ic, nc = prim
            floored = Fraction(floor(nc))
            # coprime integer coeffs (already guaranteed by _primitive)
            g = 0
            for x in ic.values():
                g = gcd(g, abs(int(x)))
            if g != 1:
                return False
            return same_form(ic, floored, f.coeffs, f.const)
        if f.rule == "case_split":
            for (label, child, cfid) in f.branches:
                cfact = next((x for x in child.facts if x.fid == cfid), None)
                if cfact is None:
                    return False
                # child assumption list
                child_asm = []
                for x in child.facts:
                    if x.rule == "assumption":
                        child_asm.append((x.coeffs, x.const, x.rel))
                if not check(cfact, child, child_asm):
                    return False
                # merged bound must be no stronger than each branch bound
                if cfact.rel == ">=" and f.rel == ">=":
                    if cfact.bound() < f.bound():
                        return False
            return True
        if f.rule == "lemma":                      # v0.7 §2
            lem = LEMMAS.get(f.lemma_cnum)
            if lem is None:
                return False
            # the asserted conclusion must match this lemma's proven conclusion
            if not (same_form(lem["coeffs"], lem["const"], f.coeffs, f.const)
                    and lem["rel"] == f.rel):
                return False
            prems = lem["premises"]
            if len(f.deps) != len(prems):
                return False
            # each premise must be entailed by its cited (and itself valid) dep
            for pr, d in zip(prems, f.deps):
                dep = fid_map.get(d)
                if dep is None or not check(dep, local_ctx, local_asm):
                    return False
                if not _dep_entails_premise(dep, pr):
                    return False
            return True
        return False

    try:
        local_asm = [(x.coeffs, x.const, x.rel) for x in ctx.facts
                     if x.rule == "assumption"]
        ok = check(fact, ctx, local_asm)
        return ok, "ok" if ok else "recheck failed"
    except Exception as exc:  # pragma: no cover
        return False, f"recheck exception: {exc}"


# ════════════════════════════════════════════════════════════════════════════
# Evaluating variables on a real p-vector (for soundness regression)
# ════════════════════════════════════════════════════════════════════════════
def vars_from_pvec(pvec: dict) -> dict:
    """Compute all deduction variables exactly from a face vector.

    ``pvec`` maps face size (int or str) -> count.  W_tail/J_tail are the exact
    weighted sums over k > M_MAX; large faces p_7..p_{M_MAX} are individual."""
    mm = inventory.M_MAX
    p = {int(k): int(v) for k, v in pvec.items()}
    vals = {"p_3": p.get(3, 0), "p_4": p.get(4, 0), "p_5": p.get(5, 0),
            "p_6": p.get(6, 0)}
    for k in range(7, mm + 1):
        vals[f"p_{k}"] = p.get(k, 0)
    vals[inventory.TAIL_VAR] = sum(v for k, v in p.items() if k > mm)
    vals["f_2"] = sum(v for k, v in p.items() if k >= 3)
    vals["W_tail"] = sum((k - 6) * v for k, v in p.items() if k > mm)
    vals["J_tail"] = sum(((k + 1) // 2 - 6) * v for k, v in p.items() if k > mm)
    return {k: Fraction(v) for k, v in vals.items()}
