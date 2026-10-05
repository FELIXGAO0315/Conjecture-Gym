"""Python counterpart of Inventory.lean and HexLemmas.lean.

Holds ONLY the axiom base.  No inference actions (those are in ``deducer.py``).

The faces k = 7 .. M_MAX are listed individually (``p_7 … p_{M_MAX}``) and the
remaining faces k > M_MAX are collected in a single tail variable
``sum_pk_after_p{M_MAX}``.  ``M_MAX`` is configurable:

  * M_MAX = 6  → no individual large faces; the tail ``sum_pk_after_p6`` =
                 Σ_{k≥7} p_k, matching the original repository's variable system.
  * M_MAX = 10 → p_7 … p_10 individual, tail ``sum_pk_after_p10`` = Σ_{k≥11} p_k.

Proof-only auxiliary tail weights (over k > M_MAX):
    W_tail = Σ_{k>M_MAX} (k-6) p_k ;  J_tail = Σ_{k>M_MAX} (⌊(k+1)/2⌋-6) p_k

All coefficients were checked against Inventory.lean:
  Euler:   3 p_3 = 12 - 2 p_4 - p_5 + Σ_{k≥7}(k-6) p_k
  Jučovič: 3 p_6 ≥ 12 - 2 p_4 - 3 p_5 + Σ_{k≥7}(⌊(k+1)/2⌋-6) p_k   (if f_2 ≥ 7)
  Barnette:2 p_6 ≥ 4 + p_3 - p_5 - 2 Σ_{k≥7} p_k                   (if Σ_{k≥7}p_k ≥ 3)

Tail-lemma constants are derived from M_MAX (minima over k > M_MAX):
    W      ≥ (M_MAX-5)·tail            (k-6 ≥ M_MAX-5)
    J      ≥ (⌊(M_MAX+2)/2⌋-6)·tail    (⌊(k+1)/2⌋-6 ; may be negative, e.g. -2 at M_MAX=6)
    W - J  ≥ (⌊(M_MAX+1)/2⌋)·tail      (⌊k/2⌋)
    2 J    ≥ W - 6·tail                 (2⌊(k+1)/2⌋ ≥ k, always)
"""

from __future__ import annotations

from fractions import Fraction

# Largest face size listed individually; the tail covers k > M_MAX.
M_MAX = 10

# tail variable name tracks M_MAX: Σ_{k>M_MAX} p_k
TAIL_VAR = f"sum_pk_after_p{M_MAX}"

# large-face variables p_7 .. p_{M_MAX} (empty when M_MAX < 7)
_LARGE = [f"p_{k}" for k in range(7, M_MAX + 1)]

# ── Variable set ────────────────────────────────────────────────────────────
PROP_VARS = ["p_3", "p_4", "p_5", "p_6"] + _LARGE + [TAIL_VAR, "f_2"]
AUX_VARS = ["W_tail", "J_tail"]
ALL_VARS = PROP_VARS + AUX_VARS

# Non-negativity axioms (J_tail is NOT non-negative in general — at M_MAX = 6 its
# per-face weight can be -2 — so it is excluded; its lower bound is tail_juc_lower).
NONNEG_VARS = ["p_3", "p_4", "p_5", "p_6"] + _LARGE + [TAIL_VAR]

# Euler / Jučovič per-face coefficients for k = 7..M_MAX
_EULER_LARGE = {f"p_{k}": (k - 6) for k in range(7, M_MAX + 1)}
_JUC_LARGE = {f"p_{k}": ((k + 1) // 2 - 6) for k in range(7, M_MAX + 1)}

# tail-lemma constants (minima of the per-face weights over k > M_MAX)
_C_EXCESS = M_MAX - 5                 # min (k-6)
_C_JUC_LOWER = (M_MAX + 2) // 2 - 6   # min (⌊(k+1)/2⌋-6)  (e.g. -2 at M_MAX=6, 0 at 10)
_C_UPPER = (M_MAX + 1) // 2           # min ⌊k/2⌋


def _lin(**terms) -> dict[str, Fraction]:
    return {v: Fraction(c) for v, c in terms.items() if Fraction(c) != 0}


def _lind(d) -> dict[str, Fraction]:
    return {v: Fraction(c) for v, c in d.items() if Fraction(c) != 0}


# ── Inventory entries ───────────────────────────────────────────────────────
INVENTORY: list[dict] = []

# 1. Euler / Jučovič edge-count equation (sphere, g = 0):
#    3 p_3 = 12 - 2 p_4 - p_5 + Σ_{k=7..M_MAX}(k-6)p_k + W_tail
_euler = {"p_3": 3, "p_4": 2, "p_5": 1, "W_tail": -1}
for v, c in _EULER_LARGE.items():
    _euler[v] = -c
INVENTORY.append({
    "name": "Juc_EulerFormula", "lean_name": "Juc_EulerFormula",
    "source": "Inventory.lean", "kind": "equality",
    "conclusion": {"coeffs": _lind(_euler), "rel": "=", "rhs": 12},
})

# 2. Jučovič inequality (first conjunct), triggered by f_2 >= 7:
#    3 p_6 >= 12 - 2 p_4 - 3 p_5 + Σ_{k=7..M_MAX}(⌊(k+1)/2⌋-6)p_k + J_tail
_juc = {"p_6": 3, "p_4": 2, "p_5": 3, "J_tail": -1}
for v, c in _JUC_LARGE.items():
    _juc[v] = -c
INVENTORY.append({
    "name": "JucovicTheorem", "lean_name": "JucovicTheorem",
    "source": "Inventory.lean", "kind": "conditional",
    "hypothesis": {"coeffs": _lin(f_2=1), "rel": ">=", "rhs": 7},
    "conclusion": {"coeffs": _lind(_juc), "rel": ">=", "rhs": 12},
})

# 3. Barnette alternate p_6 bound, triggered by Σ_{k≥7} p_k >= 3:
#    2 p_6 >= 4 + p_3 - p_5 - 2 Σ_{k≥7} p_k
_tail_count = {v: 1 for v in _LARGE + [TAIL_VAR]}
_barn = {"p_6": 2, "p_3": -1, "p_5": 1}
for v in _LARGE + [TAIL_VAR]:
    _barn[v] = 2
INVENTORY.append({
    "name": "Barnette_P6Bound", "lean_name": "Barnette_P6Bound",
    "source": "Inventory.lean", "kind": "conditional",
    "hypothesis": {"coeffs": _lind(_tail_count), "rel": ">=", "rhs": 3},
    "conclusion": {"coeffs": _lind(_barn), "rel": ">=", "rhs": 4},
})

# 4. face_split:  f_2 = p_3 + p_4 + p_5 + p_6 + Σ_{k=7..M_MAX} p_k + tail
_face = {"f_2": 1, "p_3": -1, "p_4": -1, "p_5": -1, "p_6": -1, TAIL_VAR: -1}
for v in _LARGE:
    _face[v] = -1
INVENTORY.append({
    "name": "face_split", "lean_name": "face_split", "source": "HexLemmas.lean",
    "kind": "equality",
    "conclusion": {"coeffs": _lind(_face), "rel": "=", "rhs": 0},
})

# 5. Tail lemmas (k > M_MAX), constants derived from M_MAX.
INVENTORY.append({
    "name": "tail_excess", "lean_name": "tail_excess", "source": "HexLemmas.lean",
    "kind": "inequality",
    "conclusion": {"coeffs": _lin(W_tail=1, **{TAIL_VAR: -_C_EXCESS}),
                   "rel": ">=", "rhs": 0},
})
# J_tail lower bound (replaces the old J≥0 "nonneg" — at M_MAX=6 J can be negative)
INVENTORY.append({
    "name": "tail_juc_lower", "lean_name": "tail_juc_lower",
    "source": "HexLemmas.lean", "kind": "inequality",
    "conclusion": {"coeffs": _lin(J_tail=1, **{TAIL_VAR: -_C_JUC_LOWER}),
                   "rel": ">=", "rhs": 0},
})
INVENTORY.append({
    "name": "tail_juc_upper", "lean_name": "tail_juc_upper",
    "source": "HexLemmas.lean", "kind": "inequality",
    "conclusion": {"coeffs": _lin(W_tail=1, J_tail=-1, **{TAIL_VAR: -_C_UPPER}),
                   "rel": ">=", "rhs": 0},
})
INVENTORY.append({
    "name": "tail_juc_half", "lean_name": "tail_juc_half",
    "source": "HexLemmas.lean", "kind": "inequality",
    "conclusion": {"coeffs": _lin(J_tail=2, W_tail=-1, **{TAIL_VAR: 6}),
                   "rel": ">=", "rhs": 0},
})

# 6. Non-negativity.
for _v in NONNEG_VARS:
    INVENTORY.append({
        "name": f"nonneg_{_v}", "lean_name": None, "source": "HexLemmas.lean",
        "kind": "inequality",
        "conclusion": {"coeffs": _lin(**{_v: 1}), "rel": ">=", "rhs": 0},
    })

INVENTORY_BY_NAME = {e["name"]: e for e in INVENTORY}
CONDITIONAL_THEOREMS = [e for e in INVENTORY if e["kind"] == "conditional"]

# the Barnette trigger expression (used by the deducer's case splitting)
TAIL_COUNT_VARS = _LARGE + [TAIL_VAR]
