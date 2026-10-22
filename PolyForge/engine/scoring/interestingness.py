"""Interestingness score for an invariant (in)equality conjecture (GRAFFITI-style).

The IRIS score (``iris.py``) saturates — its rank term sits at ~1 for almost every
conjecture, so T+R+L clusters at 1.0 and cannot tell an interesting bound from a
boring one.  This companion follows the Fajtlowicz / DeLaViña (GRAFFITI) notion of
an interesting invariant bound directly.  A bound is interesting when it is

    (a) SHARP   — often *near* equality across the objects satisfying its premises
                  (i.e. "best possible", not chronically loose),
    (b) ATTAINED— met with *exact* equality by at least one object, and
    (c) BROAD   — couples several invariants rather than just two.

All three are measured on the same dataset iris used (objects satisfying the
premises), so this is a drop-in companion computed right beside ``iris_score``.

    sharpness = mean over dataset of 1/(1+slack)     slack ≥ 0 (0 = exact equality)
    tightness = 1 − exp(−touch)                       touch = #objects at equality
    breadth   = clip((n_invariants − 2)/3, 0, 1)      2 vars → 0, 5+ vars → 1
    score     = 0.50·sharpness + 0.25·tightness + 0.25·breadth      ∈ [0, 1]

It is ORTHOGONAL to hardness (proof cost): a bound can be hard to prove yet loose
and boring (low score), or cheap to prove yet sharp and broad (high score).  On the
v1.4.2 graph record it has real spread (sd ≈ 0.10) where iris is flat at 1.0.
"""
from __future__ import annotations

import math


def _slack(coeffs: dict, rel: str, rhs: int, feat: tuple, feature_vars) -> int:
    lhs = sum(int(coeffs.get(v, 0)) * feat[i] for i, v in enumerate(feature_vars))
    if rel == ">=":
        return lhs - rhs
    if rel == "<=":
        return rhs - lhs
    if rel == "=":
        return abs(lhs - rhs)
    raise ValueError(rel)


def interestingness(conclusion: dict, dataset_features: list, feature_vars,
                    n_invariants: int) -> dict:
    """``dataset_features``: integer feature tuples of the objects satisfying ALL of
    the conjecture's premises (the domain pre-filters, exactly as for ``iris_score``).
    ``conclusion``: ``{coeffs, rel, rhs}`` (rel defaults to ">=", the internal form).
    ``n_invariants``: number of distinct invariant variables in premises + conclusion.

    Returns the score and its components; an empty dataset scores 0."""
    coeffs = conclusion["coeffs"]
    rel = conclusion.get("rel", ">=")
    rhs = int(conclusion["rhs"])
    nd = len(dataset_features)
    if nd == 0:
        return {"score": 0.0, "sharpness": 0.0, "tightness": 0.0,
                "breadth": 0.0, "dataset_size": 0}
    slacks = [max(0, _slack(coeffs, rel, rhs, f, feature_vars)) for f in dataset_features]
    sharpness = sum(1.0 / (1.0 + s) for s in slacks) / nd
    touch = sum(1 for s in slacks if s == 0)
    tightness = 1.0 - math.exp(-touch)
    breadth = max(0.0, min(1.0, (n_invariants - 2) / 3.0))
    score = 0.50 * sharpness + 0.25 * tightness + 0.25 * breadth
    return {"score": score, "sharpness": sharpness, "tightness": tightness,
            "breadth": breadth, "dataset_size": nd}
