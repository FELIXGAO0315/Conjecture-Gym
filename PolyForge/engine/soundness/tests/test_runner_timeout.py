"""v1.4.7 STEP 1: the lake_runner timeout must kill the WHOLE process group, so an
orphaned grandchild holding stdout cannot block communicate() forever (the v1.4.6 hang).
"""
import subprocess
import time

from PolyForge.engine.soundness.lean_batch import Goal, Verdict, _timed_group_run, verify

_MARK = "pf_grandchild_313371"


def _alive():
    r = subprocess.run(["pgrep", "-f", _MARK], capture_output=True, text=True)
    return [p for p in r.stdout.split() if p]


def test_group_kill_returns_and_leaves_no_grandchild(tmp_path):
    for p in _alive():
        subprocess.run(["kill", "-9", p])
    # a shell that backgrounds a grandchild (sleep) holding stdout, then itself sleeps:
    # without group-kill, SIGTERM to the shell leaves the grandchild holding the pipe.
    cmd = ["bash", "-c", f"sleep 313371 & exec -a {_MARK} sleep 313371"]
    t0 = time.time()
    rc, out = _timed_group_run(cmd, cwd=str(tmp_path), timeout=2.0, grace=3.0)
    dt = time.time() - t0
    assert dt < 2.0 + 3.0 + 6.0, f"did not return promptly: {dt:.1f}s"   # (a)
    assert "PF_BEGIN" not in out and rc == 124                           # no summary
    time.sleep(0.5)
    assert _alive() == [], f"grandchildren survived: {_alive()}"         # (c)


def test_timeout_maps_to_unknown(tmp_path):
    # a runner that always times out -> verify() must return UNKNOWN (fail-closed) (b)
    def hang_runner(source, timeout):
        return _timed_group_run(["bash", "-c", "sleep 313371"], cwd=str(tmp_path),
                                timeout=1.0, grace=2.0)
    res = verify([Goal("g", "(1:Int) ≤ 2", "omega")], "import Mathlib", hang_runner,
                 timeout=1.0, max_batch=4)
    assert res["g"].verdict is Verdict.UNKNOWN
    for p in _alive():
        subprocess.run(["kill", "-9", p])


def test_parse_summary_empty_axioms_is_proven():
    # v1.4.7 regression: a PROVEN declaration with an EMPTY axiom set prints a trailing
    # tab ("name\tPRESENT\t"); parse_summary must read it as PROVEN, not drop the batch.
    from PolyForge.engine.soundness.lean_batch import parse_summary, Verdict
    nonce = "deadbeefdeadbeefdeadbeef"
    def nm(x):
        return f"pf{nonce}_{x}"
    out = (f"file.lean:9:0: info: PF_BEGIN_{nonce}\n"
           f"{nm('g0')}\tPRESENT\t\n"             # proven, zero axioms (trailing tab)
           f"{nm('g1')}\tPRESENT\tpropext\n"
           f"{nm('g2')}\tMISSING\t\n"
           f"PF_END_{nonce}\n")
    rows = parse_summary(out, nonce, [nm("g0"), nm("g1"), nm("g2")])
    assert rows is not None, "empty-axioms PROVEN line must not drop the batch"
    assert rows[nm("g0")].verdict is Verdict.PROVEN and rows[nm("g0")].axioms == ()
    assert rows[nm("g1")].verdict is Verdict.PROVEN
    assert rows[nm("g2")].verdict is Verdict.NOT_PROVEN
