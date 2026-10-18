"""v1.5 R2 — the supervisor: process-group kill on stall, and checkpoint/resume.

Covers the two mandated cases: a hung grandchild (whole group must be killed) and
kill-then-resume (the job resumes from its checkpoint and eventually completes).
"""
import os
import subprocess
import sys
import textwrap
import time
from pathlib import Path

import pytest

from pf_trust.supervise import (
    read_checkpoint, run_resumable, supervise_once, write_checkpoint,
)

REPO = str(Path(__file__).resolve().parents[2])
_MARK = "pf_super_grandchild_919191"


def _env():
    e = dict(os.environ)
    e["PYTHONPATH"] = REPO + os.pathsep + e.get("PYTHONPATH", "")
    return e


def _alive():
    r = subprocess.run(["pgrep", "-f", _MARK], capture_output=True, text=True)
    return [p for p in r.stdout.split() if p]


def _write(p: Path, text: str) -> Path:
    p.write_text(textwrap.dedent(text))
    return p


def test_checkpoint_roundtrip_is_atomic(tmp_path):
    ck = tmp_path / "ck.json"
    assert read_checkpoint(ck, {"i": 0}) == {"i": 0}
    write_checkpoint(ck, {"i": 7})
    assert read_checkpoint(ck) == {"i": 7}


def test_hung_grandchild_is_killed(tmp_path):
    for p in _alive():
        subprocess.run(["kill", "-9", p])
    # A job that beats ONCE, spawns a marked grandchild holding on, then hangs forever
    # without beating. The supervisor must detect the stall and kill the WHOLE group.
    job = _write(tmp_path / "job.sh", f"""\
        #!/bin/bash
        python3 -c "from pf_trust.supervise import Heartbeat; Heartbeat('{tmp_path}/hb').beat()"
        ( exec -a {_MARK} sleep 999 ) &
        sleep 999
    """)
    os.chmod(job, 0o755)
    t0 = time.time()
    res = supervise_once(["bash", str(job)], cwd=REPO,
                         heartbeat_path=tmp_path / "hb", wall_limit=60,
                         stall_limit=3, log_path=tmp_path / "log", poll=1,
                         env=_env())
    dt = time.time() - t0
    assert res.outcome == "stalled", res
    assert dt < 30, f"took too long: {dt:.1f}s"
    time.sleep(1)
    assert _alive() == [], f"grandchildren survived the group kill: {_alive()}"


def test_wall_timeout_kills_even_while_beating(tmp_path):
    # A job that beats forever but never finishes must be killed at the wall limit.
    job = _write(tmp_path / "job.sh", f"""\
        #!/bin/bash
        for i in $(seq 1 100); do
          python3 -c "from pf_trust.supervise import Heartbeat; Heartbeat('{tmp_path}/hb').beat()"
          sleep 1
        done
    """)
    os.chmod(job, 0o755)
    res = supervise_once(["bash", str(job)], cwd=REPO,
                         heartbeat_path=tmp_path / "hb", wall_limit=3,
                         stall_limit=60, log_path=tmp_path / "log", poll=1,
                         env=_env())
    assert res.outcome == "timeout", res


def test_kill_then_resume_completes(tmp_path):
    # Each run bumps a checkpoint counter, beats once, then HANGS (stops beating) until
    # the counter reaches N, when it writes `done` and exits 0. The supervisor must keep
    # killing the stalled runs and resuming until the job completes from its checkpoint.
    job = _write(tmp_path / "job.py", f"""\
        import sys, time
        from pf_trust.supervise import Heartbeat, read_checkpoint, write_checkpoint
        HB, CK, DONE, N = "{tmp_path}/hb", "{tmp_path}/ck.json", "{tmp_path}/done", 3
        st = read_checkpoint(CK, {{"i": 0}})
        i = st["i"] + 1
        write_checkpoint(CK, {{"i": i}})
        Heartbeat(HB).beat({{"i": i}})
        if i >= N:
            open(DONE, "w").write("done")
            sys.exit(0)
        time.sleep(10000)   # hang: force a stall-kill, then resume
    """)
    res = run_resumable([sys.executable, str(job)], cwd=REPO,
                        heartbeat_path=tmp_path / "hb", done_path=tmp_path / "done",
                        log_path=tmp_path / "log", wall_limit=60, stall_limit=3,
                        max_restarts=10, poll=1, env=_env())
    assert res.outcome == "completed", res
    assert res.restarts >= 2, res          # needed 2 kills before the 3rd run finished
    assert read_checkpoint(tmp_path / "ck.json") == {"i": 3}


def test_clean_job_completes_without_restart(tmp_path):
    job = _write(tmp_path / "job.py", f"""\
        from pf_trust.supervise import Heartbeat
        Heartbeat("{tmp_path}/hb").beat()
        open("{tmp_path}/done", "w").write("ok")
    """)
    res = run_resumable([sys.executable, str(job)], cwd=REPO,
                        heartbeat_path=tmp_path / "hb", done_path=tmp_path / "done",
                        log_path=tmp_path / "log", wall_limit=30, stall_limit=10,
                        max_restarts=3, poll=1, env=_env())
    assert res.outcome == "completed" and res.restarts == 0, res
