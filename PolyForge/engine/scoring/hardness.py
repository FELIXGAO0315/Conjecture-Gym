"""Hardness score for a conjecture (domain-agnostic).

    hardness = proof_difficulty / statement_length

The weights are module-level constants so they can be re-tuned later.  The set
of inventory-*theorem* names (which carry the heavier ``W_INVENTORY`` weight)
and the names of auxiliary variables are domain-specific, so they are passed in
by the caller (defaulting to empty, i.e. everything is an "other step").
"""

from __future__ import annotations

# ── proof-difficulty weights ────────────────────────────────────────────────
W_CASE_SPLIT = 3.0      # per case split (by_cases)
W_INVENTORY = 2.0       # per Inventory *theorem* invocation (domain-supplied set)
W_ROUNDING = 2.0        # per integer-rounding step (omega)
W_PRODUCT = 2.0         # v1.2 §VII.1: per product step (mul_nonneg envelope)
W_AUX_VAR = 1.0         # per distinct auxiliary variable used
W_OTHER_STEP = 0.5      # per remaining step (premise / assumption / combination /
                        # domain lemma / non-negativity)


def _walk(steps):
    """Yield every step, descending into case-split branches."""
    for s in steps:
        yield s
        if s.get("rule") == "case_split":
            for case in s.get("cases", []):
                yield from _walk(case.get("steps", []))


def proof_difficulty(steps, inventory_theorems=(), aux_vars=()) -> float:
    inventory_theorems = set(inventory_theorems)
    aux_vars = set(aux_vars)
    n_case = 0
    n_inv = 0
    n_round = 0
    n_prod = 0
    n_other = 0
    aux_used = set()
    for s in _walk(steps):
        rule = s.get("rule")
        for v in s.get("coeffs", {}):
            if v in aux_vars:
                aux_used.add(v)
        if rule == "case_split":
            n_case += 1
        elif s.get("inventory") in inventory_theorems:
            n_inv += 1                       # one of the domain's inventory theorems
        elif rule == "rounding":
            n_round += 1
        elif rule == "product":              # v1.2 §VII.1
            n_prod += 1
        else:  # premise, assumption, combination, domain lemma, non-negativity
            n_other += 1
    return (
        W_CASE_SPLIT * n_case
        + W_INVENTORY * n_inv
        + W_ROUNDING * n_round
        + W_PRODUCT * n_prod
        + W_AUX_VAR * len(aux_used)
        + W_OTHER_STEP * n_other
    )


def proof_structure_stats(steps, inventory_theorems=()) -> dict:
    """v0.6.5 §3: structural stats of the FINAL proof (proof.steps) — number of
    case splits, maximum case-split nesting depth, number of integer-rounding steps,
    and number of Inventory-theorem invocations.  Used for difficulty tiering."""
    inventory_theorems = set(inventory_theorems)

    def walk(steps, depth):
        nc = ncond = nbnb = mcd = nr = nt = npr = 0
        for s in steps:
            rule = s.get("rule")
            if s.get("inventory") in inventory_theorems:
                nt += 1
            if rule == "rounding":
                nr += 1
            if rule == "product":                     # v1.2 §VII.2
                npr += 1
            if rule == "case_split":
                nc += 1
                if s.get("split_kind") == "bnb":      # v0.6.6: branch-and-bound split
                    nbnb += 1
                else:
                    ncond += 1
                sub = depth + 1
                maxd = sub
                for case in s.get("cases", []):
                    cc, ccd, cbd, cmd, cr, ct, cp = walk(case.get("steps", []), sub)
                    nc += cc; ncond += ccd; nbnb += cbd; nr += cr; nt += ct; npr += cp
                    maxd = max(maxd, cmd)
                mcd = max(mcd, maxd)
        return nc, ncond, nbnb, mcd, nr, nt, npr
    nc, ncond, nbnb, mcd, nr, nt, npr = walk(steps, 0)
    return {"case_splits": nc, "case_splits_conditional": ncond,
            "case_splits_bnb": nbnb, "max_nest_depth": mcd,
            "roundings": nr, "inventory_theorems": nt, "product_steps": npr}


def statement_length(premises, conclusion) -> int:
    n = len(premises)
    for pr in premises:
        n += sum(1 for c in pr["coeffs"].values() if c != 0)
    n += sum(1 for c in conclusion["coeffs"].values() if c != 0)
    return n


def hardness(steps, premises, conclusion, inventory_theorems=(), aux_vars=()) -> float:
    length = statement_length(premises, conclusion)
    if length == 0:
        return 0.0
    return proof_difficulty(steps, inventory_theorems, aux_vars) / length
