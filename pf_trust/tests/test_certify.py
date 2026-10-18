"""v1.5 PHASE C3/C4 — the z3 two-sided certificate + pure-Python re-check."""
from fractions import Fraction

import pytest

from pf_trust.certify import entailment_status, recheck_witness


def test_entailed_is_unsat_no_witness():
    # a>=5 entails a>=3
    r = entailment_status([({"a": 1}, ">=", 5)], ({"a": 1}, ">=", 3))
    assert r["status"] == "entailed" and r["witness"] is None


def test_refuted_yields_verified_integer_witness():
    # a>=3 does NOT entail a>=5: witness a=3 (or 4) with premise true and goal false
    r = entailment_status([({"a": 1}, ">=", 3)], ({"a": 1}, ">=", 5))
    assert r["status"] == "refuted"
    w = r["witness"]
    assert all(isinstance(v, int) for v in w.values())
    assert r["recheck"]["ok"]
    # the premise holds and the goal fails under the witness
    assert w["a"] >= 3 and not (w["a"] >= 5)


def test_integer_tightening_entailment():
    # 2a >= 1 over integers means a >= 1 (since a is integral), so it entails a >= 1.
    r = entailment_status([({"a": 2}, ">=", 1)], ({"a": 1}, ">=", 1))
    assert r["status"] == "entailed"
    # over rationals a=1/2 would satisfy premise and fail goal; the INTEGER domain is
    # what makes this entailed — confirms we are deciding over Z, not Q.


def test_equality_and_combination():
    # a + b == 10 and a >= 7  entails  b <= 3
    facts = [({"a": 1, "b": 1}, "==", 10), ({"a": 1}, ">=", 7)]
    assert entailment_status(facts, ({"b": 1}, "<=", 3))["status"] == "entailed"
    r = entailment_status(facts, ({"b": 1}, "<=", 2))
    assert r["status"] == "refuted" and r["recheck"]["ok"]


def test_recheck_rejects_a_bad_witness():
    # a>=3 ⊭ a>=5, but a=10 is NOT a counterexample (goal holds): recheck must say not ok.
    out = recheck_witness([({"a": 1}, ">=", 3)], ({"a": 1}, ">=", 5), {"a": 10})
    assert not out["ok"] and out["all_premises_hold"] and not out["goal_fails"]


def test_recheck_is_exact_fraction_arithmetic():
    # large coefficients: no float rounding
    facts = [({"x": 1000000007}, ">=", 1000000007)]
    goal = ({"x": 1}, ">=", 1)
    assert entailment_status(facts, goal)["status"] == "entailed"
    assert recheck_witness(facts, ({"x": 1}, ">=", 2), {"x": 1})["ok"]


def test_non_integer_inputs_are_rejected_not_truncated():
    # v1.5 audit hardening: a float must RAISE, never be silently truncated.
    with pytest.raises(TypeError):
        recheck_witness([({"a": 1}, ">=", 0)], ({"a": 1}, ">=", 1), {"a": 2.9})
    with pytest.raises(TypeError):
        recheck_witness([({"a": 1.5}, ">=", 0)], ({"a": 1}, ">=", 1), {"a": 2})
    with pytest.raises(TypeError):
        entailment_status([({"a": 1}, ">=", 0.5)], ({"a": 1}, ">=", 1))
