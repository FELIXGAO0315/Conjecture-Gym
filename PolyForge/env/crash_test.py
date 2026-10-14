#!/usr/bin/env python3
"""PolyForge v1.4.2 §E4 crash / run-safety test (zero human intervention).

Exercises, on a throwaway record directory (POLYFORGE_GRAPH_RECORD):
  1. token rejection  — a stale/orphan writer (old token) is refused (§E2);
  2. flock exclusion  — a second run cannot acquire the record lock, and is told the
     holder PID (§E1);
  3. PDEATHSIG + atomicity + lock release — SIGKILL the running generator mid-run; its
     worker processes die automatically (§E3), the record contains only complete
     C-dirs (atomic writes), and the lock is released so a restart needs zero manual
     steps (§E4).

Usage: python -m PolyForge.env.crash_test
"""
import os, signal, subprocess, sys, tempfile, time
from pathlib import Path

REPO = Path("/home/felix_gao/Conjecture-Gym")


def _check(name, ok):
    print(f"  [{'PASS' if ok else 'FAIL'}] {name}", flush=True)
    return ok


def main():
    tmp = Path(tempfile.mkdtemp(prefix="pf_crash_"))
    rec = tmp / "record"
    # PYTHONHASHSEED=0 so `import run` in helper subprocesses does NOT trigger run.py's
    # determinism re-exec (which would relaunch `python -m run` and print usage).
    env = dict(os.environ, POLYFORGE_GRAPH_RECORD=str(rec), PYTHONHASHSEED="0")
    allok = True

    # ── 1. token rejection ────────────────────────────────────────────────────
    print("1. token rejection (orphan/stale writer)", flush=True)
    r = subprocess.run([sys.executable, "-c", f"""
import sys; sys.path.insert(0,"{REPO}")
from pathlib import Path
from PolyForge.generator import generator as CG
rec=Path("{rec}"); rec.mkdir(parents=True, exist_ok=True)
(rec/".run_token").write_text("TOKEN_A")
CG.set_run_token("TOKEN_A")
data={{"id":"C1","created_at":"x","generator":{{}},"conjecture":{{"formula":"f","natural_language":"n"}},
      "proof":{{"steps":[]}},"iris":{{"T":0,"R":0,"L":0,"score":0}},"hardness":0.0,"attained":"yes",
      "touch":0,"lean":{{"status":"compiled"}}}}
CG.write_record(data,"theorem C1 := by trivial",rec)          # token matches -> OK
print("write-with-matching-token OK:", (rec/"C1").exists())
(rec/".run_token").write_text("TOKEN_B")                      # a restore rotated the token
try:
    CG.write_record(dict(data,id="C2"),"theorem C2 := by trivial",rec)
    print("STALE_WRITE_NOT_REJECTED")
except CG.StaleWriterError as e:
    print("stale writer rejected OK")
"""], capture_output=True, text=True, env=env)
    out = r.stdout + r.stderr
    allok &= _check("matching-token write succeeds", "write-with-matching-token OK: True" in out)
    allok &= _check("stale-token write rejected", "stale writer rejected OK" in out
                    and "STALE_WRITE_NOT_REJECTED" not in out)

    # ── 2. flock exclusion ──────────────────────────────────────────────────────
    print("2. flock exclusion (second run aborts, names holder)", flush=True)
    holder = subprocess.Popen([sys.executable, "-c", f"""
import sys,time; sys.path.insert(0,"{REPO}")
from pathlib import Path
import run as R
fd,tok=R.acquire_record_lock(Path("{rec}"))
print("holder up", flush=True); time.sleep(20)
"""], stdout=subprocess.PIPE, text=True, env=env)
    time.sleep(4)
    r2 = subprocess.run([sys.executable, "-c", f"""
import sys; sys.path.insert(0,"{REPO}")
from pathlib import Path
import run as R
try:
    R.acquire_record_lock(Path("{rec}"))
    print("LOCK_NOT_EXCLUSIVE")
except SystemExit as e:
    print("second acquire aborted code", e.code)
"""], capture_output=True, text=True, env=env)
    o2 = r2.stdout + r2.stderr
    allok &= _check("second acquirer aborted (exit 4) naming holder",
                    "second acquire aborted code 4" in o2 and "locked by another run" in o2
                    and "pid=" in o2)
    holder.terminate()
    try:
        holder.wait(timeout=5)
    except Exception:
        holder.kill()

    # ── 3. PDEATHSIG + atomicity + lock release ─────────────────────────────────
    print("3. SIGKILL mid-run → workers die, record atomic, lock released", flush=True)
    import shutil
    if rec.exists():
        shutil.rmtree(rec)
    proc = subprocess.Popen([sys.executable, "-m", "run", "polyforge", "graph", "2",
                             "--max-groups", "6", "--seed", "2024"],
                            cwd=str(REPO), stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, env=env)
    # wait for the Pool workers to spawn
    kids = []
    for _ in range(60):
        time.sleep(1)
        try:
            out = subprocess.run(["pgrep", "-P", str(proc.pid)], capture_output=True, text=True)
            kids = [int(x) for x in out.stdout.split()]
        except Exception:
            kids = []
        if kids:
            break
    print(f"   main pid {proc.pid}, worker children: {kids}", flush=True)
    os.kill(proc.pid, signal.SIGKILL)                 # hard crash of the generator
    time.sleep(4)
    def alive(pid):
        try:
            os.kill(pid, 0); return True
        except OSError:
            return False
    workers_dead = all(not alive(k) for k in kids) if kids else True
    allok &= _check("worker processes died with the parent (PDEATHSIG)", workers_dead)
    # record atomicity: no leftover temp dirs, every C-dir has its 3 files
    partial = list(rec.glob(".C*.tmp")) if rec.exists() else []
    cdirs = [d for d in rec.iterdir() if d.is_dir() and d.name.startswith("C")] if rec.exists() else []
    complete = all((d / f"{d.name}.json").exists() and (d / f"{d.name}.lean").exists()
                   and (d / f"{d.name}.md").exists() for d in cdirs)
    allok &= _check(f"record atomic (no partial tmp dirs; {len(cdirs)} complete C-dirs)",
                    not partial and complete)
    # lock released → a restart can acquire with zero manual steps
    r3 = subprocess.run([sys.executable, "-c", f"""
import sys; sys.path.insert(0,"{REPO}")
from pathlib import Path
import run as R
fd,tok=R.acquire_record_lock(Path("{rec}"))
print("restart acquired lock OK token", tok)
"""], capture_output=True, text=True, env=env)
    allok &= _check("lock released after crash — restart acquires with zero steps",
                    "restart acquired lock OK" in (r3.stdout + r3.stderr))

    shutil.rmtree(tmp, ignore_errors=True)
    print("\nCRASH TEST: " + ("ALL PASS" if allok else "FAILURES"), flush=True)
    sys.exit(0 if allok else 1)


if __name__ == "__main__":
    main()
