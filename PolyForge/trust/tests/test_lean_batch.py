import re

import pytest

from PolyForge.trust.lean_batch import Goal, Verdict, render_batch, selftest, verify
from PolyForge.trust.tests.fake_lean import make_runner, old_method

HEADER = "import Mathlib"
NONCE = "0123456789abcdef0123456789abcdef"


def goals(n_false, n_true_after):
    gs = [Goal(f"f{i}", f"({i + 1} : Int) ≤ 0", "omega") for i in range(n_false)]
    gs += [Goal(f"t{i}", f"({i} : Int) ≤ {i + 1}", "omega") for i in range(n_true_after)]
    gs += [Goal(f"g{i}", f"({i + 5} : Int) ≤ {i}", "omega") for i in range(n_true_after)]
    return gs


def truth(g):
    return g.name.startswith("t")


@pytest.mark.parametrize("mode", ["ok", "truncate", "abort"])
def test_correct_under_every_maxerrors_mode(mode):
    gs = goals(150, 10)
    res = verify(gs, HEADER, make_runner(mode), max_batch=400)
    for g in gs:
        want = Verdict.PROVEN if truth(g) else Verdict.NOT_PROVEN
        assert res[g.name].verdict is want, (mode, g.name, res[g.name])


def test_old_method_is_fooled_by_truncation():
    gs = goals(150, 10)
    r = render_batch(HEADER, gs, NONCE)
    _, out = make_runner("truncate")(r.source, 10)
    old = old_method(r.source, out)  # keyed by INTERNAL (nonce-namespaced) names
    truth_by_internal = {m.group(1): int(m.group(2)) <= int(m.group(3))
                         for m in re.finditer(r"theorem (\S+) : \((-?\d+) : Int\) ≤ (-?\d+)", r.source)}
    wrongly_proven = [n for n, proven in old.items() if proven and not truth_by_internal[n]]
    assert wrongly_proven, "fake runner should reproduce the v1.4.4 bug"


def test_broken_summary_fails_closed():
    gs = goals(3, 3)
    res = verify(gs, HEADER, make_runner("broken_summary"))
    assert all(r.verdict is Verdict.UNKNOWN for r in res.values())


def test_selftest_passes_on_fake_and_detects_broken():
    assert selftest(HEADER, make_runner("truncate"))["ok"]
    assert not selftest(HEADER, make_runner("broken_summary"))["ok"]


def test_rejects_bad_names():
    with pytest.raises(ValueError):
        render_batch(HEADER, [Goal("bad name", "True", "trivial")], NONCE)
    with pytest.raises(ValueError):
        render_batch(HEADER, [Goal("x", "True", "t"), Goal("x", "True", "t")], NONCE)


def test_rejects_short_nonce():
    # B1: a nonce that is too short (not >=16 hex) is refused — it could not reliably
    # namespace generated theorems away from Mathlib / attacker-chosen names.
    with pytest.raises(ValueError):
        render_batch(HEADER, [Goal("g", "True", "trivial")], "abcd")


def test_rc_nonzero_is_not_treated_as_crash():
    gs = goals(1, 1)
    res = verify(gs, HEADER, make_runner("ok"))
    assert res["t0"].verdict is Verdict.PROVEN and res["f0"].verdict is Verdict.NOT_PROVEN
