"""v1.4.7 STEP 1: the lake_runner timeout must kill the WHOLE process group, so an
orphaned grandchild holding stdout cannot block communicate() forever (the v1.4.6 hang).
"""
import subprocess
import time

from pf_trust.lean_batch import Goal, Verdict, _timed_group_run, verify

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
