"""PolyForge Lean verifier (v1.3 §III).

A fast, batched, resident-REPL verifier for PolyForge proof submissions.  A
submission is *only* the proof (the tactic block after ``by``); the verifier
prepends the task's fixed ``lean_header`` and ``lean_statement`` so the submitter
cannot alter the statement text.  Scoring matches openai-math: reward 1 iff the
statement is exactly the reference statement, the proof is accepted by the Lean
kernel, and it depends only on the standard axioms (``propext``, ``Quot.sound``,
``Classical.choice``); otherwise reward 0, with a ``status`` explaining why.

Layered anti-cheating (any failing layer ⇒ reward 0):

  forbidden          static scan: no top-level commands / ``set_option`` / ``sorry`` …
  compile_error      the proof does not compile (or leaves a ``sorry``)
  heartbeats         exceeded ``maxHeartbeats`` (resource limit)
  timeout            exceeded the wall-clock limit (second safety net)
  env_modified       the proof added constants other than the target theorem
  statement_mismatch the proved type differs from the reference statement's type
  bad_axioms         the proof depends on a non-standard axiom (e.g. ``sorryAx``)
  ok                 reward 1

The verifier loads Mathlib + the domain's Lean library once per resident REPL
process and reuses that environment for every submission.  Multiple processes run
in parallel; each restarts after a configurable number of checks (and on crash).
"""

from __future__ import annotations

import json
import os
import queue
import re
import subprocess
import threading
import time
from dataclasses import dataclass, field
from pathlib import Path

from . import tasks as T

_ROOT = Path(__file__).resolve().parents[1]
_REPL_BIN_DEFAULT = _ROOT / "env" / "vendor" / "repl" / ".lake" / "build" / "bin" / "repl"

STANDARD_AXIOMS = {"propext", "Quot.sound", "Classical.choice"}

# §III.3: resource limits.  The default heartbeat budget is set well above the
# worst-case consumption of any reference proof (see README / verification report
# for the measurement).  Lean's own default is 200000.
DEFAULT_MAX_HEARTBEATS = 400000
DEFAULT_TIMEOUT = 60.0            # wall-clock seconds per submission
DEFAULT_RESTART_EVERY = 200       # recycle a REPL process after this many checks

# A resident REPL with Mathlib loaded uses ~6.5 GB RSS, so the default process
# count is sized from total RAM (≈7 GB/process) capped by the core count.
_MEM_PER_PROC_GB = 7.0


def default_nprocs() -> int:
    try:
        cores = os.cpu_count() or 2
        with open("/proc/meminfo") as f:
            total_kb = int(next(l for l in f if l.startswith("MemTotal")).split()[1])
        by_mem = int((total_kb / 1024 / 1024) / _MEM_PER_PROC_GB)
        return max(1, min(cores - 2, by_mem))
    except Exception:
        return 1

# ── static anti-cheat (§III.2a) ────────────────────────────────────────────────
_TOP_LEVEL_CMDS = [
    "theorem", "lemma", "def", "abbrev", "instance", "axiom", "example",
    "structure", "class", "inductive", "macro", "macro_rules", "syntax",
    "notation", "infix", "infixl", "infixr", "prefix", "postfix", "elab",
    "open", "namespace", "section", "end", "attribute", "import", "variable",
    "universe",
]
_LINE_CMD_RE = re.compile(r"^\s*(?:" + "|".join(_TOP_LEVEL_CMDS) + r")\b")
_HASH_CMD_RE = re.compile(r"^\s*#")
_ANYWHERE_RE = re.compile(r"\bset_option\b|debug\.|\bsorry\b|\badmit\b")


def static_check(proof: str) -> str | None:
    """Return an offending token/pattern if the proof is statically forbidden,
    else ``None``.  Matches whole words (not substrings) for the top-level
    commands; flags any ``set_option`` / ``debug.`` / ``sorry`` / ``admit`` and any
    ``#``-command anywhere on a line."""
    for line in proof.splitlines():
        if _LINE_CMD_RE.match(line):
            return _LINE_CMD_RE.match(line).group(0).strip()
        if _HASH_CMD_RE.match(line):
            return "#command"
        m = _ANYWHERE_RE.search(line)
        if m:
            return m.group(0)
    return None


# ── combined post-compile metaprogram (§III.2b/c/d) ───────────────────────────
# One command run in the submission's environment: lists the locally-added
# constants (environment diff), the proved type under ``pp.all`` (type check), and
# the axiom dependencies (axiom check), emitted as JSON between @@@ markers.
_META = r'''open Lean Elab Command Meta in
run_cmd do
  let env ← getEnv
  let locals := env.constants.map₂.toList.map (fun p => p.1.toString)
  let ax ← liftCoreM (collectAxioms `%NAME%)
  let axs := ax.toList.map (·.toString)
  let tyStr ← liftTermElabM do
    let ci ← getConstInfo `%NAME%
    withOptions (fun o => o.setBool `pp.all true) (do return toString (← Meta.ppExpr ci.type))
  let out := Json.mkObj [("locals", toJson locals), ("type", toJson tyStr), ("axioms", toJson axs)]
  logInfo m!"@@@{out.compress}@@@"
'''

_HEARTBEAT_HINTS = ("maxHeartbeats", "deterministic timeout", "maximum recursion depth")


@dataclass
class VerifyResult:
    task_id: str
    reward: float
    status: str
    error: str = ""
    elapsed: float = 0.0

    def to_dict(self):
        return {"task_id": self.task_id, "reward": self.reward, "status": self.status,
                "error": self.error, "elapsed": round(self.elapsed, 4)}


# ── one resident REPL process ──────────────────────────────────────────────────
class ReplProcess:
    def __init__(self, cfg: T.DomainConfig, repl_bin: Path, restart_every: int):
        self.cfg = cfg
        self.repl_bin = repl_bin
        self.restart_every = restart_every
        self.proc: subprocess.Popen | None = None
        self.env0: int | None = None
        self.baseline: set[str] = set()
        self.checks = 0
        self.load_time = 0.0
        self._q: queue.Queue | None = None
        self._reader: threading.Thread | None = None
        self.start()

    def start(self):
        self.stop()
        t0 = time.time()
        self.proc = subprocess.Popen(
            ["lake", "env", str(self.repl_bin)],
            cwd=str(self.cfg.lean_dir),
            stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            text=True, bufsize=1,
        )
        # a dedicated reader thread feeds stdout lines into a queue, so _send can
        # enforce a wall-clock deadline without the select()/buffered-readline race.
        self._q = queue.Queue()
        self._reader = threading.Thread(target=self._read_loop,
                                        args=(self.proc.stdout, self._q), daemon=True)
        self._reader.start()
        r = self._send({"cmd": self.cfg.repl_preamble}, timeout=600)
        self.env0 = r["env"]
        self.baseline = set(self._query_locals(self.env0))
        self.load_time = time.time() - t0
        self.checks = 0

    def stop(self):
        if self.proc is not None:
            try:
                self.proc.stdin.close()
            except Exception:
                pass
            try:
                self.proc.terminate()
                self.proc.wait(timeout=5)
            except Exception:
                try:
                    self.proc.kill()
                except Exception:
                    pass
            self.proc = None

    @staticmethod
    def _read_loop(stdout, q: queue.Queue):
        try:
            for line in iter(stdout.readline, ""):
                q.put(line)
        finally:
            q.put(None)        # sentinel: stream closed

    # low-level JSON exchange over stdin/stdout with a wall-clock deadline
    def _send(self, obj: dict, timeout: float) -> dict:
        assert self.proc is not None and self._q is not None
        self.proc.stdin.write(json.dumps(obj) + "\n\n")
        self.proc.stdin.flush()
        deadline = time.time() + timeout
        lines: list[str] = []
        while True:
            remaining = deadline - time.time()
            if remaining <= 0:
                raise TimeoutError("wall-clock timeout")
            try:
                line = self._q.get(timeout=remaining)
            except queue.Empty:
                raise TimeoutError("wall-clock timeout")
            if line is None:
                raise BrokenPipeError("REPL closed")
            if line.strip() == "":
                if lines:
                    break
                continue
            lines.append(line)
        return json.loads("".join(lines))

    def _query_locals(self, env: int) -> list[str]:
        # bare locals dump (the target theorem doesn't exist yet in env0)
        cmd = ("open Lean Elab Command in\nrun_cmd do\n"
               "  let env ← getEnv\n"
               "  let locals := env.constants.map₂.toList.map (fun p => p.1.toString)\n"
               "  logInfo m!\"@@@{(Lean.toJson locals).compress}@@@\"\n")
        r = self._send({"cmd": cmd, "env": env}, timeout=120)
        return _extract_json(r)

    def verify(self, statement: str, proof: str, theorem_name: str,
               ref_type: str, max_heartbeats: int, timeout: float) -> VerifyResult:
        """Verify one submission in this process's loaded environment.  Assumes the
        static check already passed.  May raise TimeoutError/BrokenPipeError (the
        caller restarts and retries)."""
        indented = "\n".join(("  " + ln) if ln else "" for ln in proof.split("\n"))
        cmd = f"set_option maxHeartbeats {max_heartbeats} in\n{statement}\n{indented}"
        t0 = time.time()
        r = self._send({"cmd": cmd, "env": self.env0}, timeout=timeout)
        self.checks += 1
        msgs = r.get("messages", []) or []
        errors = [m for m in msgs if m.get("severity") == "error"]
        if errors:
            blob = " ".join(m.get("data", "") for m in errors)
            status = "heartbeats" if any(h in blob for h in _HEARTBEAT_HINTS) else "compile_error"
            return VerifyResult(theorem_name, 0.0, status, _short(blob), time.time() - t0)
        if r.get("sorries"):
            return VerifyResult(theorem_name, 0.0, "compile_error", "proof left a sorry",
                                time.time() - t0)
        env1 = r["env"]
        meta = _META.replace("%NAME%", theorem_name)
        rm = self._send({"cmd": meta, "env": env1}, timeout=timeout)
        info = _extract_obj(rm)
        if info is None:
            merr = " ".join(m.get("data", "") for m in rm.get("messages", [])
                            if m.get("severity") == "error")
            return VerifyResult(theorem_name, 0.0, "compile_error",
                                "introspection failed: " + _short(merr), time.time() - t0)
        # (b) environment diff
        new = [c for c in info["locals"] if c not in self.baseline]
        prefix = theorem_name + "."
        stray = [c for c in new if c != theorem_name and not c.startswith(prefix)]
        if stray:
            return VerifyResult(theorem_name, 0.0, "env_modified",
                                "unexpected new constants: " + ", ".join(sorted(stray)[:8]),
                                time.time() - t0)
        # (c) type / statement match
        if info["type"] != ref_type:
            return VerifyResult(theorem_name, 0.0, "statement_mismatch",
                                "proved type differs from the reference statement",
                                time.time() - t0)
        # (d) axioms
        bad = [a for a in info["axioms"] if a not in STANDARD_AXIOMS]
        if bad:
            return VerifyResult(theorem_name, 0.0, "bad_axioms",
                                "non-standard axioms: " + ", ".join(bad), time.time() - t0)
        return VerifyResult(theorem_name, 1.0, "ok", "", time.time() - t0)

    def ref_type(self, statement: str, theorem_name: str, timeout: float) -> str:
        """Elaborate the reference statement (with a ``sorry`` body) in the clean
        environment and return its ``pp.all`` type string.  The resulting env is
        discarded, so env0 stays clean."""
        cmd = f"{statement} sorry"
        r = self._send({"cmd": cmd, "env": self.env0}, timeout=timeout)
        env1 = r["env"]
        meta = _META.replace("%NAME%", theorem_name)
        rm = self._send({"cmd": meta, "env": env1}, timeout=timeout)
        info = _extract_obj(rm)
        if info is None:
            raise RuntimeError(f"failed to elaborate reference type for {theorem_name}")
        return info["type"]


def _short(s: str, n: int = 400) -> str:
    s = " ".join(s.split())
    return s if len(s) <= n else s[:n] + "…"


def _extract_obj(resp: dict):
    for m in resp.get("messages", []) or []:
        d = m.get("data", "")
        if "@@@" in d:
            return json.loads(d.split("@@@")[1])
    return None


def _extract_json(resp: dict):
    for m in resp.get("messages", []) or []:
        d = m.get("data", "")
        if "@@@" in d:
            return json.loads(d.split("@@@")[1])
    return []


# ── the verifier: process pool + reference-type cache ──────────────────────────
class Verifier:
    def __init__(self, domain: str, nprocs: int | None = None,
                 repl_bin: Path | None = None,
                 max_heartbeats: int = DEFAULT_MAX_HEARTBEATS,
                 timeout: float = DEFAULT_TIMEOUT,
                 restart_every: int = DEFAULT_RESTART_EVERY,
                 split_seed: int = 1337):
        self.cfg = T.domain_config(domain)
        self.domain = domain
        self.repl_bin = Path(repl_bin or os.environ.get("POLYFORGE_REPL_BIN", _REPL_BIN_DEFAULT))
        if not self.repl_bin.exists():
            raise FileNotFoundError(
                f"REPL binary not found at {self.repl_bin}; build it with "
                f"PolyForge/env/setup_repl.sh (or set POLYFORGE_REPL_BIN)")
        self.max_heartbeats = max_heartbeats
        self.timeout = timeout
        self.restart_every = restart_every
        self.nprocs = max(1, nprocs if nprocs is not None else default_nprocs())
        # task index (task_id -> task dict) and reference-type cache
        self._tasks = T.tasks_by_id(T.build_tasks(domain, split_seed=split_seed))
        self._ref_cache: dict[str, str] = {}
        self._procs: list[ReplProcess] = []

    # lazy process pool
    def _ensure_procs(self, n: int):
        while len(self._procs) < min(n, self.nprocs):
            self._procs.append(ReplProcess(self.cfg, self.repl_bin, self.restart_every))

    def _proc(self, i: int) -> ReplProcess:
        self._ensure_procs(i + 1)
        return self._procs[i % len(self._procs)]

    def close(self):
        for p in self._procs:
            p.stop()
        self._procs = []

    def __enter__(self):
        return self

    def __exit__(self, *a):
        self.close()

    def tasks(self) -> dict:
        return self._tasks

    def _ref_type(self, proc: ReplProcess, task: dict) -> str:
        tid = task["task_id"]
        if tid not in self._ref_cache:
            self._ref_cache[tid] = proc.ref_type(task["lean_statement"],
                                                  task["theorem_name"], self.timeout)
        return self._ref_cache[tid]

    def _verify_on(self, proc: ReplProcess, task: dict, proof: str) -> VerifyResult:
        tid = task["task_id"]
        bad = static_check(proof)
        if bad is not None:
            return VerifyResult(tid, 0.0, "forbidden", f"forbidden token: {bad}")
        attempts = 0
        while True:
            attempts += 1
            try:
                ref = self._ref_type(proc, task)
                res = proc.verify(task["lean_statement"], proof, task["theorem_name"],
                                  ref, self.max_heartbeats, self.timeout)
                res.task_id = tid
                if proc.checks >= proc.restart_every:
                    proc.start()
                return res
            except TimeoutError:
                proc.start()                      # kill the stuck process
                return VerifyResult(tid, 0.0, "timeout",
                                    f"exceeded {self.timeout}s wall-clock limit")
            except (BrokenPipeError, json.JSONDecodeError, KeyError) as e:
                self._ref_cache.pop(tid, None)
                proc.start()
                if attempts >= 2:
                    return VerifyResult(tid, 0.0, "compile_error", f"REPL error: {_short(str(e))}")

    def verify(self, task_id: str, proof: str) -> VerifyResult:
        task = self._tasks.get(task_id)
        if task is None:
            return VerifyResult(task_id, 0.0, "unknown_task", f"no such task {task_id}")
        return self._verify_on(self._proc(0), task, proof)

    def verify_batch(self, items: list[tuple[str, str]]) -> list[VerifyResult]:
        """Verify a list of (task_id, proof).  Uses the process pool; the order of
        the results matches the input.

        Each REPL process is driven by exactly one thread (its stdin/stdout are not
        concurrency-safe); items are partitioned round-robin across processes."""
        n = len(items)
        if self.nprocs <= 1 or n <= 1:
            return [self.verify(tid, pf) for tid, pf in items]
        self._ensure_procs(min(self.nprocs, n))
        P = len(self._procs)
        results: list[VerifyResult | None] = [None] * n
        buckets: list[list[int]] = [[] for _ in range(P)]
        for idx in range(n):
            buckets[idx % P].append(idx)

        def run(pi: int):
            proc = self._procs[pi]
            for idx in buckets[pi]:
                tid, pf = items[idx]
                task = self._tasks.get(tid)
                if task is None:
                    results[idx] = VerifyResult(tid, 0.0, "unknown_task", f"no such task {tid}")
                else:
                    results[idx] = self._verify_on(proc, task, pf)

        threads = [threading.Thread(target=run, args=(pi,)) for pi in range(P)]
        for t in threads:
            t.start()
        for t in threads:
            t.join()
        return results


# ── CLI ─────────────────────────────────────────────────────────────────────────
def _main(argv=None):
    import argparse
    ap = argparse.ArgumentParser(description="PolyForge Lean verifier")
    ap.add_argument("domain")
    ap.add_argument("--task", help="task_id to verify")
    ap.add_argument("--proof", help="file containing the proof (tactic block after `by`)")
    ap.add_argument("--batch", help="jsonl with {task_id, proof} per line")
    ap.add_argument("--nprocs", type=int, default=1)
    ap.add_argument("--max-heartbeats", type=int, default=DEFAULT_MAX_HEARTBEATS)
    ap.add_argument("--timeout", type=float, default=DEFAULT_TIMEOUT)
    args = ap.parse_args(argv)

    with Verifier(args.domain, nprocs=args.nprocs,
                  max_heartbeats=args.max_heartbeats, timeout=args.timeout) as V:
        if args.batch:
            items = []
            with open(args.batch) as f:
                for line in f:
                    line = line.strip()
                    if line:
                        o = json.loads(line)
                        items.append((o["task_id"], o["proof"]))
            for res in V.verify_batch(items):
                print(json.dumps(res.to_dict(), ensure_ascii=False))
        elif args.task and args.proof:
            proof = Path(args.proof).read_text()
            res = V.verify(args.task, proof)
            print(json.dumps(res.to_dict(), ensure_ascii=False))
        else:
            ap.error("provide --task and --proof, or --batch")


if __name__ == "__main__":
    _main()
