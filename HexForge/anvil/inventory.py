"""Python counterpart of Inventory.lean and HexLemmas.lean (v0.6.1).

Holds ONLY the axiom base.  No inference actions (those are in ``deducer.py``).

v0.6.1: the large faces are listed individually, p_7 … p_{M_MAX}, plus a single
tail ``sum_pk_after_p10`` = Σ_{k > M_MAX} p_k.  The Inventory theorems are
unchanged — their k ≥ 7 sums are merely written out for k = 7..M_MAX with the
k > M_MAX part kept as a tail.  M_MAX is configurable.

Every coefficient below was checked against Inventory.lean:
  Euler:   Σ_{k≥7} (k−6) p_k      → p_7 + 2 p_8 + 3 p_9 + 4 p_10 + W_tail
  Jučovič: Σ_{k≥7} (⌊(k+1)/2⌋−6)  → −2 p_7 − 2 p_8 − p_9 − p_10 + J_tail
  tail k≥11:  k−6 ≥ 5,  ⌊(k+1)/2⌋−6 ≥ 0,  ⌊k/2⌋ ≥ 5,  2⌊(k+1)/2⌋ ≥ k
"""

from __future__ import annotations

from fractions import Fraction

# Largest face size listed individually; the tail covers k > M_MAX.
M_MAX = 10

# large-face variables p_7 .. p_{M_MAX}
_LARGE = [f"p_{k}" for k in range(7, M_MAX + 1)]

# ── Variable set ────────────────────────────────────────────────────────────
PROP_VARS = ["p_3", "p_4", "p_5", "p_6"] + _LARGE + ["sum_pk_after_p10", "f_2"]
# Proof-only auxiliary tail weights (k > M_MAX):
#   W_tail = Σ_{k>M_MAX} (k-6) p_k ;  J_tail = Σ_{k>M_MAX} (⌊(k+1)/2⌋-6) p_k
AUX_VARS = ["W_tail", "J_tail"]
ALL_VARS = PROP_VARS + AUX_VARS

# Non-negativity axioms (J_tail's non-negativity is the tail_juc_nonneg lemma):
NONNEG_VARS = ["p_3", "p_4", "p_5", "p_6"] + _LARGE + ["sum_pk_after_p10"]

# Euler / Jučovič per-face coefficients for k = 7..M_MAX
_EULER_LARGE = {f"p_{k}": (k - 6) for k in range(7, M_MAX + 1)}        # 1,2,3,4
_JUC_LARGE = {f"p_{k}": ((k + 1) // 2 - 6) for k in range(7, M_MAX + 1)}  # -2,-2,-1,-1


def _lin(**terms) -> dict[str, Fraction]:
    return {v: Fraction(c) for v, c in terms.items() if Fraction(c) != 0}


# ── Inventory entries ───────────────────────────────────────────────────────
INVENTORY: list[dict] = []

# 1. Euler / Jučovič edge-count equation (sphere, g = 0), expanded:
#    3 p_3 = 12 - 2 p_4 - p_5 + p_7 + 2 p_8 + 3 p_9 + 4 p_10 + W_tail
_euler = {"p_3": 3, "p_4": 2, "p_5": 1, "W_tail": -1}
for v, c in _EULER_LARGE.items():
    _euler[v] = -c
INVENTORY.append({
    "name": "Juc_EulerFormula", "lean_name": "Juc_EulerFormula",
    "source": "Inventory.lean", "kind": "equality",
    "conclusion": {"coeffs": _lin(**_euler), "rel": "=", "rhs": 12},
})

# 2. Jučovič inequality (first conjunct), triggered by f_2 >= 7, expanded:
#    3 p_6 >= 12 - 2 p_4 - 3 p_5 - 2 p_7 - 2 p_8 - p_9 - p_10 + J_tail
_juc = {"p_6": 3, "p_4": 2, "p_5": 3, "J_tail": -1}
for v, c in _JUC_LARGE.items():
    _juc[v] = -c          # moving -2 p_7 etc. to the left flips sign to +2 p_7
INVENTORY.append({
    "name": "JucovicTheorem", "lean_name": "JucovicTheorem",
    "source": "Inventory.lean", "kind": "conditional",
    "hypothesis": {"coeffs": _lin(f_2=1), "rel": ">=", "rhs": 7},
    "conclusion": {"coeffs": _lin(**_juc), "rel": ">=", "rhs": 12},
})

# 3. Barnette alternate p_6 bound, triggered by (p_7+..+p_10+sum_pk_after_p10) >= 3:
#    2 p_6 >= 4 + p_3 - p_5 - 2 (p_7 + p_8 + p_9 + p_10 + sum_pk_after_p10)
_tail_count = {v: 1 for v in _LARGE + ["sum_pk_after_p10"]}
_barn = {"p_6": 2, "p_3": -1, "p_5": 1}
for v in _LARGE + ["sum_pk_after_p10"]:
    _barn[v] = 2
INVENTORY.append({
    "name": "Barnette_P6Bound", "lean_name": "Barnette_P6Bound",
    "source": "Inventory.lean", "kind": "conditional",
    "hypothesis": {"coeffs": _lin(**_tail_count), "rel": ">=", "rhs": 3},
    "conclusion": {"coeffs": _lin(**_barn), "rel": ">=", "rhs": 4},
})

# 4. face_split:  f_2 = p_3 + p_4 + ... + p_10 + sum_pk_after_p10
_face = {"f_2": 1, "p_3": -1, "p_4": -1, "p_5": -1, "p_6": -1,
         "sum_pk_after_p10": -1}
for v in _LARGE:
    _face[v] = -1
INVENTORY.append({
    "name": "face_split", "lean_name": "face_split", "source": "HexLemmas.lean",
    "kind": "equality",
    "conclusion": {"coeffs": _lin(**_face), "rel": "=", "rhs": 0},
})

# 5. Tail lemmas (k > M_MAX).
INVENTORY.append({
    "name": "tail_excess", "lean_name": "tail_excess", "source": "HexLemmas.lean",
    "kind": "inequality",
    "conclusion": {"coeffs": _lin(W_tail=1, sum_pk_after_p10=-5), "rel": ">=", "rhs": 0},
})
INVENTORY.append({
    "name": "tail_juc_nonneg", "lean_name": "tail_juc_nonneg",
    "source": "HexLemmas.lean", "kind": "inequality",
    "conclusion": {"coeffs": _lin(J_tail=1), "rel": ">=", "rhs": 0},
})
INVENTORY.append({
    "name": "tail_juc_upper", "lean_name": "tail_juc_upper",
    "source": "HexLemmas.lean", "kind": "inequality",
    "conclusion": {"coeffs": _lin(W_tail=1, J_tail=-1, sum_pk_after_p10=-5),
                   "rel": ">=", "rhs": 0},
})
INVENTORY.append({
    "name": "tail_juc_half", "lean_name": "tail_juc_half",
    "source": "HexLemmas.lean", "kind": "inequality",
    "conclusion": {"coeffs": _lin(J_tail=2, W_tail=-1, sum_pk_after_p10=6),
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
TAIL_COUNT_VARS = _LARGE + ["sum_pk_after_p10"]
