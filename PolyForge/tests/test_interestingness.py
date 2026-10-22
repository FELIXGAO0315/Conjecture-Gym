"""The interestingness metric must actually discriminate (iris did not)."""
from PolyForge.engine.scoring.interestingness import interestingness

FV = ["a", "b", "c"]


def _concl(coeffs, rel=">=", rhs=0):
    return {"coeffs": coeffs, "rel": rel, "rhs": rhs}


def test_empty_dataset_scores_zero():
    assert interestingness(_concl({"a": 1}), [], FV, 2)["score"] == 0.0


def test_sharp_bound_beats_loose_bound():
    # a ≥ 0, dataset where a is always exactly 0 → perfectly sharp + attained
    sharp = interestingness(_concl({"a": 1}, ">=", 0), [(0, 5, 5), (0, 1, 2)], FV, 2)
    # a ≥ 0 but a is always large → chronically loose, never attained
    loose = interestingness(_concl({"a": 1}, ">=", 0), [(9, 5, 5), (12, 1, 2)], FV, 2)
    assert sharp["sharpness"] == 1.0 and sharp["tightness"] > 0.6
    assert loose["sharpness"] < 0.2 and loose["tightness"] == 0.0
    assert sharp["score"] > loose["score"]


def test_breadth_rewards_more_invariants():
    pts = [(3, 1, 2)]
    two = interestingness(_concl({"a": 1}, ">=", 0), pts, FV, 2)["breadth"]
    five = interestingness(_concl({"a": 1}, ">=", 0), pts, FV, 5)["breadth"]
    assert two == 0.0 and five == 1.0


def test_score_bounded_and_le_handled():
    r = interestingness(_concl({"a": 1}, "<=", 10), [(10, 0, 0), (8, 0, 0)], FV, 4)
    assert 0.0 <= r["score"] <= 1.0
    assert r["tightness"] > 0.0           # (10 ≤ 10) attained by the first point
