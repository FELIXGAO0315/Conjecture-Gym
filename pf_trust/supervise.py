"""Liveness-in-code for every long job (v1.5 R2).

A long job (the 319×319 matrix, the baselines, L4) must never be babysat by hand.
It runs under ``run_resumable``:

  * the child runs in its OWN process session/group (``start_new_session=True``),
    so on stall or timeout we kill the WHOLE group — no orphaned grandchild can
    keep running or hold a pipe open (the v1.4.6 hang class);
  * a wall-clock limit bounds each attempt;
  * the job updates a HEARTBEAT file at least every ``beat_every`` seconds; if the
    supervisor sees no heartbeat for ``stall_limit`` seconds (default 10 min) it
    kills the group;
  * the job CHECKPOINTS its own progress; when the supervisor relaunches it
    (after a stall/kill) it resumes from the checkpoint. The loop repeats until
    the job signals completion (writes ``done_path`` or exits 0) or a restart /
    global-deadline budget is exhausted.

Timing uses integer seconds only (no floats in any control decision). The job's
math pipeline is unaffected by this module.

CLI:  python -m pf_trust.supervise --heartbeat H --done D --wall N --stall M \
                                    --log L [--max-restarts K] -- CMD ARGS...
"""
from __future__ import annotations

import argparse
import json
import os
import signal
import subprocess
import threading
import sys
import time
from dataclasses import dataclass, asdict
from pathlib import Path
from typing import Sequence


def _now() -> int:
    return int(time.time())


def _mtime(path: Path) -> int | None:
    try:
        return int(path.stat().st_mtime)
    except FileNotFoundError:
        return None


def _kill_group(pid: int, grace: int = 5) -> None:
    """SIGTERM the process group, wait a grace period, then SIGKILL. Idempotent."""
    try:
        pgid = os.getpgid(pid)
    except ProcessLookupError:
        return
    for sig in (signal.SIGTERM, signal.SIGKILL):
        try:
            os.killpg(pgid, sig)
        except ProcessLookupError:
            return
        # wait up to `grace` seconds for the group leader to die before escalating
        for _ in range(max(1, grace)):
            time.sleep(1)
            try:
                os.killpg(pgid, 0)       # probe: raises when the group is gone
            except ProcessLookupError:
                return


# ─────────────────────────── heartbeat / checkpoint helpers (for the JOB) ────
class Heartbeat:
    """Used INSIDE a job to prove liveness. Call ``beat()`` at least every
    ``beat_every`` seconds (well under the supervisor's stall_limit)."""

    def __init__(self, path: str | os.PathLike):
        self.path = Path(path)
        self.path.parent.mkdir(parents=True, exist_ok=True)

    def beat(self, progress: dict | None = None) -> None:
        payload = {"t": _now(), "pid": os.getpid()}
        if progress is not None:
            payload["progress"] = progress
        # Unique tmp per (pid, thread) so concurrent beaters never race on os.replace.
        tmp = self.path.with_suffix(self.path.suffix + f".{os.getpid()}.{threading.get_ident()}.tmp")
        tmp.write_text(json.dumps(payload))
        os.replace(tmp, self.path)      # atomic; bumps mtime


def write_checkpoint(path: str | os.PathLike, obj) -> None:
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(json.dumps(obj))
    os.replace(tmp, path)               # atomic: a kill mid-write never corrupts it


def read_checkpoint(path: str | os.PathLike, default=None):
    try:
        return json.loads(Path(path).read_text())
    except (FileNotFoundError, json.JSONDecodeError):
        return default


# ─────────────────────────── the supervisor ──────────────────────────────────
@dataclass
class SuperviseResult:
    outcome: str            # "completed" | "timeout" | "stalled" | "failed"
    returncode: int | None
    restarts: int
    elapsed: int
    detail: str = ""

    def ok(self) -> bool:
        return self.outcome == "completed"


def supervise_once(argv: Sequence[str], *, cwd: str, heartbeat_path: Path,
                   wall_limit: int, stall_limit: int, log_path: Path,
                   done_path: Path | None = None, poll: int = 2,
                   env: dict | None = None) -> SuperviseResult:
    """Run ``argv`` once under supervision. Kills the whole group on wall-timeout
    or heartbeat stall. stdout+stderr are appended to ``log_path`` (so a noisy job
    cannot deadlock on a full pipe while we poll)."""
    log_path.parent.mkdir(parents=True, exist_ok=True)
    start = _now()
    last_activity = start
    with open(log_path, "a") as logf:
        logf.write(f"\n==== supervise_once start {start} argv={list(argv)} ====\n")
        logf.flush()
        proc = subprocess.Popen(list(argv), cwd=cwd, stdout=logf, stderr=logf,
                                start_new_session=True, env=env)
        try:
            while True:
                rc = proc.poll()
                if rc is not None:
                    done = (done_path is not None and done_path.exists())
                    if rc == 0 or done:
                        return SuperviseResult("completed", rc, 0, _now() - start)
                    return SuperviseResult("failed", rc, 0, _now() - start,
                                           f"exit {rc}")
                now = _now()
                if now - start >= wall_limit:
                    _kill_group(proc.pid)
                    return SuperviseResult("timeout", None, 0, now - start,
                                           f"wall {wall_limit}s exceeded")
                m = _mtime(heartbeat_path)
                if m is not None and m > last_activity:
                    last_activity = m
                if now - last_activity >= stall_limit:
                    _kill_group(proc.pid)
                    return SuperviseResult("stalled", None, 0, now - start,
                                           f"no heartbeat for {stall_limit}s")
                time.sleep(poll)
        finally:
            if proc.poll() is None:
                _kill_group(proc.pid)


def run_resumable(argv: Sequence[str], *, cwd: str, heartbeat_path: str | os.PathLike,
                  done_path: str | os.PathLike, log_path: str | os.PathLike,
                  wall_limit: int = 6 * 3600, stall_limit: int = 600,
                  max_restarts: int = 20, global_deadline: int | None = None,
                  poll: int = 2, env: dict | None = None) -> SuperviseResult:
    """Supervise ``argv``, resuming after every stall/timeout/transient failure until
    it completes (writes ``done_path`` or exits 0) or the restart / global-deadline
    budget is exhausted. The JOB is responsible for checkpoint/resume; the supervisor
    just relaunches the same argv, which the job uses to continue from its checkpoint."""
    hb, done, log = Path(heartbeat_path), Path(done_path), Path(log_path)
    if done.exists():
        return SuperviseResult("completed", 0, 0, 0, "already done")
    t0 = _now()
    attempt = 0
    last: SuperviseResult | None = None
    while attempt <= max_restarts:
        if global_deadline is not None and _now() - t0 >= global_deadline:
            return SuperviseResult("timeout", None, attempt, _now() - t0,
                                   "global deadline exceeded")
        res = supervise_once(argv, cwd=cwd, heartbeat_path=hb, wall_limit=wall_limit,
                             stall_limit=stall_limit, log_path=log, done_path=done,
                             poll=poll, env=env)
        res.restarts = attempt
        res.elapsed = _now() - t0
        last = res
        if res.outcome == "completed" or done.exists():
            res.outcome = "completed"
            return res
        attempt += 1
    last = last or SuperviseResult("failed", None, 0, _now() - t0, "no attempt")
    last.outcome = "failed" if last.outcome == "failed" else last.outcome
    last.detail = (last.detail + f"; exhausted {max_restarts} restarts").strip("; ")
    return last


def _main(argv: list[str]) -> int:
    p = argparse.ArgumentParser()
    p.add_argument("--heartbeat", required=True)
    p.add_argument("--done", required=True)
    p.add_argument("--log", required=True)
    p.add_argument("--cwd", default=os.getcwd())
    p.add_argument("--wall", type=int, default=6 * 3600)
    p.add_argument("--stall", type=int, default=600)
    p.add_argument("--max-restarts", type=int, default=20)
    p.add_argument("--result", default=None, help="write SuperviseResult JSON here")
    p.add_argument("cmd", nargs=argparse.REMAINDER)
    a = p.parse_args(argv)
    cmd = a.cmd[1:] if a.cmd and a.cmd[0] == "--" else a.cmd
    if not cmd:
        p.error("no command given after --")
    res = run_resumable(cmd, cwd=a.cwd, heartbeat_path=a.heartbeat, done_path=a.done,
                        log_path=a.log, wall_limit=a.wall, stall_limit=a.stall,
                        max_restarts=a.max_restarts)
    if a.result:
        Path(a.result).write_text(json.dumps(asdict(res), indent=2))
    print(json.dumps(asdict(res)))
    return 0 if res.ok() else 1


if __name__ == "__main__":
    sys.exit(_main(sys.argv[1:]))
