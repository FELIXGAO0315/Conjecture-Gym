"""v1.5 PHASE B — real-toolchain hardening tests (B1/B4/B7 against actual Lean).

Slow (each batch compiles against Mathlib). Skipped automatically if `lake` or the
Lean project is unavailable. verify_all FULL runs these; FAST does not.
Run directly:  python -m pytest pf_trust/tests/test_hardening_real.py -v
"""
import shutil
from pathlib import Path

import pytest

from pf_trust.lean_batch import Goal, Verdict, lake_runner, selftest, verify

LEAN_DIR = Path("/home/felix_gao/Conjecture-Gym/PolyForge/domains/graph/lean")
HEADER = "import Mathlib"

pytestmark = pytest.mark.skipif(
    shutil.which("lake") is None or not (LEAN_DIR / "lean-toolchain").exists(),
    reason="real Lean toolchain not available",
)


def _runner():
    # maxErrors as defense-in-depth (speed only; correctness never depends on it)
    return lake_runner(str(LEAN_DIR), extra_args=["-D", "maxErrors=100000000"])


def test_b4_canaries_pass_on_real_toolchain():
    # If any mandatory canary misread on the real toolchain, EVERY batch would be
    # UNKNOWN. A true goal returning PROVEN and a false goal NOT_PROVEN proves the 5
    # canaries (incl. the zero-axiom / trailing-tab one) all read correctly here.
    res = verify([Goal("t", "(1 : Int) ≤ 2", "omega"),
                  Goal("f", "(2 : Int) ≤ 1", "omega")],
                 HEADER, _runner(), timeout=600.0, max_batch=50)
    assert res["t"].verdict is Verdict.PROVEN, res["t"]
    assert res["f"].verdict is Verdict.NOT_PROVEN, res["f"]


def test_b1_name_collision_with_false_statement_is_not_proven():
    # External name collides with the real Mathlib constant `Nat`; statement is FALSE.
    # Nonce namespacing declares pf<nonce>_Nat instead, which fails, so NOT_PROVEN —
    # the pre-existing `Nat` is never consulted.
    res = verify([Goal("Nat", "(2 : Int) ≤ 1", "omega")], HEADER, _runner(),
                 timeout=600.0, max_batch=50)
    assert res["Nat"].verdict is Verdict.NOT_PROVEN, res["Nat"]


def test_b1_name_collision_with_true_statement_still_certified_by_this_batch():
    # Same colliding name but a TRUE statement: PROVEN, and certified by THIS batch's
    # own declaration (nonce-namespaced), not by the Mathlib `Nat`.
    res = verify([Goal("Nat", "(1 : Int) ≤ 2", "omega")], HEADER, _runner(),
                 timeout=600.0, max_batch=50)
    assert res["Nat"].verdict is Verdict.PROVEN, res["Nat"]


def test_b7_custom_axiom_is_not_proven():
    # A goal whose proof uses a CUSTOM axiom (declared in the header) must be NOT_PROVEN:
    # collectAxioms returns the custom axiom, which is not in ALLOWED_AXIOMS.
    header = HEADER + "\naxiom pfEvilAxiom : (2 : Int) ≤ 1"
    res = verify([Goal("viaAxiom", "(2 : Int) ≤ 1", "exact pfEvilAxiom"),
                  Goal("viaOmega", "(1 : Int) ≤ 2", "omega")],
                 header, _runner(), timeout=600.0, max_batch=50)
    assert res["viaAxiom"].verdict is Verdict.NOT_PROVEN, res["viaAxiom"]
    assert res["viaOmega"].verdict is Verdict.PROVEN, res["viaOmega"]


def test_selftest_ok_on_real_toolchain():
    # The maxErrors reproduction must classify every goal correctly in one trusted batch.
    out = selftest(HEADER, _runner(), n_false=150)
    assert out["ok"], out
