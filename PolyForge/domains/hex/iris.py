"""Hex-domain IRIS features.

The feature vector for a simple 3-polytope is

    x = (p_3, p_4, p_5, p_6, [p_7 .. p_{M_MAX},] sum_pk_after_p{M_MAX}, f_2).

The generic T/R/L computation lives in ``scoring.iris``; this module supplies
the hex feature ordering and the per-object feature extraction, and wraps
``scoring.iris.iris_score`` so the rest of the hex code keeps its 3-argument
call convention.
"""

from __future__ import annotations

from ...engine.scoring import iris as _IRIS
from .inventory import M_MAX, TAIL_VAR

FEATURES = (["p_3", "p_4", "p_5", "p_6"] + [f"p_{k}" for k in range(7, M_MAX + 1)]
            + [TAIL_VAR, "f_2"])


def features_from_pvec(pvec: dict) -> tuple:
    p = {int(k): int(v) for k, v in pvec.items()}
    feats = [p.get(3, 0), p.get(4, 0), p.get(5, 0), p.get(6, 0)]
    feats += [p.get(k, 0) for k in range(7, M_MAX + 1)]
    feats.append(sum(v for k, v in p.items() if k > M_MAX))   # tail
    feats.append(sum(v for k, v in p.items() if k >= 3))       # f_2
    return tuple(feats)


def iris_score(premises: list, conclusion: dict, pool_features: list) -> dict:
    """Hex wrapper: evaluate the IRIS score with the hex ``FEATURES`` ordering."""
    return _IRIS.iris_score(premises, conclusion, pool_features, FEATURES)
