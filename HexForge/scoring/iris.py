"""IRIS score for a conjecture.

    score = T + R + L

evaluated on the *dataset* = the real p-vectors (from plantri_pool.json) that
satisfy the conjecture's premises, with feature vector

    x = (p_3, p_4, p_5, p_6, sum_pk_after_p6, f_2).

    T = |touch| / |dataset|              tightness  (fraction on the equality face)
    R = rank(touch matrix) / |touch|     independence of the touching points
    L = diam(touch) / diam(dataset)      spread of the touching points

``touch`` = the dataset points where the conclusion holds with *exact* equality
(integer arithmetic, no epsilon).  When ``touch`` is empty, T = R = L = 0.

Rank and diameter are the only places (besides the LP) where floating point is
permitted (spec §4).
"""

from __future__ import annotations

import numpy as np

from ..anvil.inventory import M_MAX

FEATURES = (["p_3", "p_4", "p_5", "p_6"] + [f"p_{k}" for k in range(7, M_MAX + 1)]
            + ["sum_pk_after_p10", "f_2"])


def features_from_pvec(pvec: dict) -> tuple:
    p = {int(k): int(v) for k, v in pvec.items()}
    feats = [p.get(3, 0), p.get(4, 0), p.get(5, 0), p.get(6, 0)]
    feats += [p.get(k, 0) for k in range(7, M_MAX + 1)]
    feats.append(sum(v for k, v in p.items() if k > M_MAX))   # tail
    feats.append(sum(v for k, v in p.items() if k >= 3))       # f_2
    return tuple(feats)


def _sat(coeffs: dict, rel: str, rhs: int, feat: tuple) -> bool:
    lhs = sum(int(coeffs.get(v, 0)) * feat[i] for i, v in enumerate(FEATURES))
    if rel == "=":
        return lhs == rhs
    if rel == ">=":
        return lhs >= rhs
    if rel == "<=":
        return lhs <= rhs
    raise ValueError(rel)


def _is_equality_point(conclusion: dict, feat: tuple) -> bool:
    coeffs, rhs = conclusion["coeffs"], int(conclusion["rhs"])
    lhs = sum(int(coeffs.get(v, 0)) * feat[i] for i, v in enumerate(FEATURES))
    return lhs == rhs


def _diameter(points: np.ndarray) -> float:
    """Max pairwise Euclidean distance.  Exact for small sets; a deterministic
    2-sweep lower-bound approximation for large ones (both numerator and
    denominator use the same rule, so the ratio stays meaningful)."""
    n = len(points)
    if n <= 1:
        return 0.0
    if n <= 3000:
        # exact, chunked to bound memory
        best = 0.0
        for i in range(0, n, 512):
            block = points[i:i + 512]
            d = np.sqrt(((block[:, None, :] - points[None, :, :]) ** 2).sum(-1))
            best = max(best, float(d.max()))
        return best
    # farthest-point double sweep (deterministic 2-approximation)
    c = points.mean(axis=0)
    a = int(np.argmax(((points - c) ** 2).sum(-1)))
    da = ((points - points[a]) ** 2).sum(-1)
    b = int(np.argmax(da))
    return float(np.sqrt(((points - points[b]) ** 2).sum(-1).max()))


def iris_score(premises: list, conclusion: dict, pool_features: list) -> dict:
    """``pool_features`` is a list of 6-tuples (one per real p-vector)."""
    dataset = [f for f in pool_features
               if all(_sat(pr["coeffs"], pr["rel"], int(pr["rhs"]), f) for pr in premises)]
    n = len(dataset)
    if n == 0:
        return {"T": 0.0, "R": 0.0, "L": 0.0, "score": 0.0,
                "dataset_size": 0, "touch_size": 0}
    touch = [f for f in dataset if _is_equality_point(conclusion, f)]
    nt = len(touch)
    if nt == 0:
        return {"T": 0.0, "R": 0.0, "L": 0.0, "score": 0.0,
                "dataset_size": n, "touch_size": 0}

    T = nt / n
    touch_arr = np.array(touch, dtype=float)
    R = float(np.linalg.matrix_rank(touch_arr)) / nt

    data_arr = np.array(dataset, dtype=float)
    diam_data = _diameter(np.unique(data_arr, axis=0))
    diam_touch = _diameter(np.unique(touch_arr, axis=0))
    L = 0.0 if diam_data == 0 else diam_touch / diam_data

    score = T + R + L
    return {"T": T, "R": R, "L": L, "score": score,
            "dataset_size": n, "touch_size": nt}
