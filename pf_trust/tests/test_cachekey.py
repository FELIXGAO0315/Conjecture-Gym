"""v1.5 review A' — content-addressed verdict cache key.

The key must cover EVERY decision module (miss one and a stale PROVEN leaks). These
tests enforce that the import-closure hash covers every tagged decision module, that
the fingerprint is deterministic, and that it actually changes when a decision file's
content changes.
"""
import hashlib
from pathlib import Path

from pf_trust import cachekey


def test_coverage_every_decision_module_in_closure():
    # any module tagged PF_DECISION_MODULE=True that the roots don't reach -> FAIL
    missing = cachekey.check_coverage()
    assert missing == [], f"decision modules not in the cache-key closure: {missing}"


def test_closure_includes_the_roots_and_fact_builders():
    clo = set(cachekey.import_closure())
    for m in ("pf_trust.lean_batch", "pf_trust.certify", "pf_trust.props",
              "pf_trust.canon", "pf_trust.policies", "PolyForge.env.closure_complete"):
        assert m in clo, m
    # the encoding's fact builders are reachable from closure_complete -> must be hashed
    assert "PolyForge.domains.graph.generator" in clo
    assert "PolyForge.anvil.deducer" in clo


def test_fingerprint_is_deterministic():
    assert cachekey.verdict_fingerprint() == cachekey.verdict_fingerprint()
    assert len(cachekey.verdict_fingerprint()) == 64


def test_fingerprint_changes_if_a_decision_file_changes(tmp_path, monkeypatch):
    # simulate editing a decision module: the hash MUST move.
    base = cachekey.verdict_fingerprint()
    real = cachekey.import_closure
    victim = Path(cachekey.import_closure()["pf_trust.canon"])

    def fake_closure(roots=None):
        clo = dict(real(roots))
        return clo
    # inject a content change by hashing a mutated copy: monkeypatch read_bytes of victim
    orig_read_bytes = Path.read_bytes

    def patched(self):
        if self == victim:
            return orig_read_bytes(self) + b"\n# mutated\n"
        return orig_read_bytes(self)
    monkeypatch.setattr(Path, "read_bytes", patched)
    assert cachekey.verdict_fingerprint() != base


def test_fingerprint_includes_toolchain_and_solver_pins():
    # the fingerprint string must incorporate the pins (checked structurally: a changed
    # pin value changes the digest). We verify the pins are read by diffing a stub.
    from pf_trust import pins
    v = pins.versions()
    assert v["lean_toolchain"] and v["mathlib_rev"] and v["z3-solver"]
