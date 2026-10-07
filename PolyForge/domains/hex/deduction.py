"""Hex-domain search configuration for the generic deduction engine.

These objects were formerly module-level constants inside ``anvil.deducer``; in
PolyForge they are the hex domain's contribution to the engine configuration
(injected via ``anvil.deducer.configure``):

    BASE_DIRECTIONS   directed objectives explored every saturation round
    SPLIT_SPECS       conditional-theorem case-split expressions + thresholds
    BNB_VARS          branch-and-bound split variables
    vars_from_pvec    exact evaluation of the deduction variables on a face
                      vector (used by the soundness regression)
"""

from __future__ import annotations

from fractions import Fraction

from . import inventory
from .inventory import PROP_VARS

# p_7..p_{M_MAX} + tail (= big_faces count)
_TAIL_COUNT = {v: 1 for v in inventory.TAIL_COUNT_VARS}


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
