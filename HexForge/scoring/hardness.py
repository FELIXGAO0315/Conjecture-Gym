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


def proof_structure_stats(steps) -> dict:
    """v0.6.5 §3: structural stats of the FINAL proof (proof.steps) — number of
    case splits, maximum case-split nesting depth, number of integer-rounding steps,
    and number of Inventory-theorem invocations.  Used for difficulty tiering."""
    def walk(steps, depth):
        nc = ncond = nbnb = mcd = nr = nt = 0
        for s in steps:
            rule = s.get("rule")
            if s.get("inventory") in INVENTORY_THEOREMS:
                nt += 1
            if rule == "rounding":
                nr += 1
            if rule == "case_split":
                nc += 1
                if s.get("split_kind") == "bnb":      # v0.6.6: branch-and-bound split
                    nbnb += 1
                else:
                    ncond += 1
                sub = depth + 1
                maxd = sub
                for case in s.get("cases", []):
                    cc, ccd, cbd, cmd, cr, ct = walk(case.get("steps", []), sub)
                    nc += cc; ncond += ccd; nbnb += cbd; nr += cr; nt += ct
                    maxd = max(maxd, cmd)
                mcd = max(mcd, maxd)
        return nc, ncond, nbnb, mcd, nr, nt
    nc, ncond, nbnb, mcd, nr, nt = walk(steps, 0)
    return {"case_splits": nc, "case_splits_conditional": ncond,
            "case_splits_bnb": nbnb, "max_nest_depth": mcd,
            "roundings": nr, "inventory_theorems": nt}


def tier_of(stats: dict) -> int:
    """v0.6.5 §3: difficulty tier (1-5) from the final proof structure.
      1: no case split, 1 rounding
      2: no case split, >=2 roundings
      3: case split, max nesting depth 1, exactly 1 case split
      4: max nesting depth 2, or >=2 case splits (nesting depth <= 2)
      5: max nesting depth >= 3"""
    nc = stats["case_splits"]
    depth = stats["max_nest_depth"]
    nr = stats["roundings"]
    if depth >= 3:
        return 5
    if nc == 0:
        return 2 if nr >= 2 else 1
    if depth == 1 and nc == 1:
        return 3
    return 4                                    # depth == 2, or (>=2 splits, depth<=2)


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
