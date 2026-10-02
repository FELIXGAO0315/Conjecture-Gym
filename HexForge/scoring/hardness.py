"""Hardness score for a conjecture.

    hardness = proof_difficulty / statement_length

The weights are module-level constants so they can be re-tuned later.
"""

from __future__ import annotations

# ── proof-difficulty weights ────────────────────────────────────────────────
W_CASE_SPLIT = 3.0      # per case split (by_cases)
W_INVENTORY = 2.0       # per Inventory *theorem* invocation (the 3 below only)
W_ROUNDING = 2.0        # per integer-rounding step (omega)
W_AUX_VAR = 1.0         # per distinct auxiliary variable (W, J) used
W_OTHER_STEP = 0.5      # per remaining step (premise / assumption / combination /
                        # HexLemmas lemma / non-negativity)

AUX_VARS = ("W", "J")

# Only these three count towards the "Inventory theorem" term; HexLemmas lemmas
# (face_split, tail_*) and non-negativity facts are "other steps".
INVENTORY_THEOREMS = ("Juc_EulerFormula", "JucovicTheorem", "Barnette_P6Bound")


def _walk(steps):
    """Yield every step, descending into case-split branches."""
    for s in steps:
        yield s
        if s.get("rule") == "case_split":
            for case in s.get("cases", []):
                yield from _walk(case.get("steps", []))


def proof_difficulty(steps) -> float:
    n_case = 0
    n_inv = 0
    n_round = 0
    n_other = 0
    aux_used = set()
    for s in _walk(steps):
        rule = s.get("rule")
        for v in s.get("coeffs", {}):
            if v in AUX_VARS:
                aux_used.add(v)
        if rule == "case_split":
            n_case += 1
        elif s.get("inventory") in INVENTORY_THEOREMS:
            n_inv += 1                       # one of the 3 Inventory theorems
        elif rule == "rounding":
            n_round += 1
        else:  # premise, assumption, combination, HexLemmas lemma, non-negativity
            n_other += 1
    return (
        W_CASE_SPLIT * n_case
        + W_INVENTORY * n_inv
        + W_ROUNDING * n_round
        + W_AUX_VAR * len(aux_used)
        + W_OTHER_STEP * n_other
    )


def statement_length(premises, conclusion) -> int:
    n = len(premises)
    for pr in premises:
        n += sum(1 for c in pr["coeffs"].values() if c != 0)
    n += sum(1 for c in conclusion["coeffs"].values() if c != 0)
    return n


def hardness(steps, premises, conclusion) -> float:
    length = statement_length(premises, conclusion)
    if length == 0:
        return 0.0
    return proof_difficulty(steps) / length
