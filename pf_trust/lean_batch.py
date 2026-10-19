"""Fail-closed batched Lean verification.

Why this exists
---------------
The v1.4.5 report found that `omega_decide_batch` decided "proven" from the
ABSENCE of error messages. Once Lean stops reporting errors (maxErrors), every
later failing goal looked proven. This module never infers success from silence.

Decision rule (the only one)
----------------------------
A goal is PROVEN only if a summary block, printed by a final `#eval` command
after all goals, lists the goal's declaration as present in the environment with
axioms contained in ALLOWED_AXIOMS (so no `sorryAx`). Everything else is
NOT_PROVEN (summary says present with sorryAx / missing) or UNKNOWN (no
trustworthy summary at all).

The batch as a whole is trusted only if:
  * the summary block (tagged with a fresh random tag) appears exactly once,
  * it lists exactly the expected declaration names,
  * the true canary is PROVEN and the false canary is NOT_PROVEN.
Otherwise the batch is split in halves and retried; a single goal that still has
no trustworthy result is UNKNOWN. Callers must treat UNKNOWN as "not proven"
whenever a wrong "proven" would be unsound (pruning, oracle reward).

What is NOT verified here
-------------------------
The Lean meta code in `_SUMMARY_TEMPLATE` was written without access to the
project's pinned toolchain. Run `selftest()` against the real toolchain first.
If the summary command does not elaborate there, the batch fails closed
(UNKNOWN everywhere), so a wrong template can cost time but cannot produce a
false "proven".
"""
from __future__ import annotations

import os
import re
import secrets
import signal
import subprocess
import tempfile
from dataclasses import dataclass
from enum import Enum
from typing import Callable, Iterable, Sequence

ALLOWED_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})
_NAME_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_]*$")
# A per-batch nonce is hex, so it can never occur in an attacker-controlled goal name
# or in Mathlib; it namespaces generated theorems and frames the summary (B1/B2).
_NONCE_RE = re.compile(r"^[0-9a-f]{16,}$")


class Verdict(str, Enum):
    PROVEN = "proven"
    NOT_PROVEN = "not_proven"
    UNKNOWN = "unknown"


@dataclass(frozen=True)
class Goal:
    name: str        # plain Lean identifier, unique within the batch
    statement: str   # Lean proposition (everything after the colon)
    proof: str       # tactic block body, e.g. "omega"; may be multi-line


@dataclass(frozen=True)
class GoalResult:
    name: str
    verdict: Verdict
    axioms: tuple[str, ...] = ()
    detail: str = ""


@dataclass(frozen=True)
class Rendered:
    """Output of render_batch (v1.5: carries the nonce namespacing + canary plan)."""
    source: str
    nonce: str
    expected: tuple[str, ...]            # INTERNAL (nonce-namespaced) names, incl. canaries
    name_map: dict                       # internal name -> external (caller-facing) name
    canary_expected: dict                # internal canary name -> expected Verdict


# runner(source_text, timeout_seconds) -> (returncode, combined stdout+stderr)
Runner = Callable[[str, float], tuple[int, str]]


# ── B4: mandatory in-batch canaries ──────────────────────────────────────────
# Every batch carries these five. Their real-toolchain axiom sets were measured
# (v1.5 Phase B probe):
#   true  : omega 1≤2            -> PROVEN, axioms {propext, Quot.sound}
#   false : omega 2≤1 (fails)    -> NOT_PROVEN
#   zero  : True by trivial      -> PROVEN, axioms ∅   (forces the EMPTY-axiom
#                                   "name\tPRESENT\t" line into EVERY batch — the
#                                   exact shape the v1.4.6 trailing-tab bug corrupted)
#   sorry : 2≤1 by sorry         -> NOT_PROVEN, axioms {sorryAx}
#   stdax : ∀p, p∨¬p by Classical.em -> PROVEN, axioms {propext,Classical.choice,Quot.sound}
# If ANY canary misreads, the whole batch is untrusted (fail-closed → split/UNKNOWN).
_CANARIES = (
    ("true",  "(1 : Int) ≤ 2",         "omega",                        Verdict.PROVEN),
    ("false", "(2 : Int) ≤ 1",         "omega",                        Verdict.NOT_PROVEN),
    ("zero",  "True",                   "trivial",                      Verdict.PROVEN),
    ("sorry", "(2 : Int) ≤ 1",         "sorry",                        Verdict.NOT_PROVEN),
    ("stdax", "∀ p : Prop, p ∨ ¬ p",   "intro p; exact Classical.em p", Verdict.PROVEN),
)


def canary_name(suffix: str, nonce: str) -> str:
    return f"pf_canary_{suffix}_{nonce}"


def _internal(name: str, nonce: str) -> str:
    """Namespace a caller-facing goal name under the per-batch nonce (B1)."""
    return f"pf{nonce}_{name}"


_SUMMARY_TEMPLATE = """\
open Lean Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let names : List Name := [{names}]
  let mut lines : Array String := #[]
  for n in names do
    if env.contains n then
      let axs ← Lean.collectAxioms n
      lines := lines.push (toString n ++ "\\tPRESENT\\t" ++ String.intercalate "," (axs.toList.map toString))
    else
      lines := lines.push (toString n ++ "\\tMISSING\\t")
  logInfo (String.intercalate "\\n" (("{begin}" :: lines.toList) ++ ["{end}"]))
"""


def _indent(text: str, n: int = 2) -> str:
    pad = " " * n
    return "\n".join(pad + line if line.strip() else line for line in text.splitlines())


def render_batch(header: str, goals: Sequence[Goal], nonce: str) -> Rendered:
    """Render a batch. Every generated theorem is namespaced under the per-batch
    ``nonce`` (B1: ``env.contains`` can then only be true for a constant THIS batch
    declared — a goal named to collide with a Mathlib constant is declared under its
    own nonce name and looked up there, so the collision cannot make it PROVEN). The
    summary is framed with nonce-bearing sentinels (B2). Canaries are appended."""
    if not _NONCE_RE.match(nonce):
        raise ValueError(f"nonce must be >=16 hex chars (got {nonce!r})")
    names = [g.name for g in goals]
    for n in names:
        if not _NAME_RE.match(n):
            raise ValueError(f"goal name is not a plain Lean identifier: {n!r}")
    if len(set(names)) != len(names):
        raise ValueError("duplicate goal names in batch")

    name_map: dict = {}
    parts = [header.rstrip(), ""]
    for g in goals:
        iname = _internal(g.name, nonce)
        name_map[iname] = g.name
        parts.append(f"theorem {iname} : {g.statement} := by\n{_indent(g.proof)}\n")

    canary_expected: dict = {}
    for suffix, statement, proof, verdict in _CANARIES:
        cname = canary_name(suffix, nonce)
        canary_expected[cname] = verdict
        parts.append(f"theorem {cname} : {statement} := by\n{_indent(proof)}\n")

    expected = tuple(name_map) + tuple(canary_expected)
    parts.append(
        _SUMMARY_TEMPLATE.format(
            names=", ".join(f"`{n}" for n in expected),
            begin=f"PF_BEGIN_{nonce}",
            end=f"PF_END_{nonce}",
        )
    )
    return Rendered("\n".join(parts), nonce, expected, name_map, canary_expected)


def parse_summary(output: str, nonce: str, expected: Sequence[str]) -> dict[str, GoalResult] | None:
    """Parse the nonce-framed summary. Returns None (→ untrusted → fail-closed) if it
    is absent, duplicated, malformed, carries a row whose name does not bear the nonce
    (B1/B2 namespace check), or does not list exactly the expected names once each."""
    begin, end = f"PF_BEGIN_{nonce}", f"PF_END_{nonce}"
    if output.count(begin) != 1 or output.count(end) != 1:
        return None
    body = output.split(begin, 1)[1].split(end, 1)[0]
    rows: dict[str, GoalResult] = {}
    for raw in body.splitlines():
        # v1.4.7: strip line-endings and spaces only, NOT tabs — a PROVEN declaration with
        # an EMPTY axiom set prints "name\tPRESENT\t" (trailing tab = empty axioms field);
        # `raw.strip()` would eat that tab, drop the batch to 2 columns and (unsoundly for
        # liveness) mark the whole batch untrusted.  An empty axiom set is legitimately
        # PROVEN (∅ ⊆ ALLOWED_AXIOMS).
        line = raw.strip(" \r\n")
        if not line:
            continue
        cols = line.split("\t")
        if len(cols) != 3 or cols[1] not in ("PRESENT", "MISSING"):
            return None
        name, status, axs = cols
        # B1/B2: a trustworthy row names a constant THIS batch declared, so its name
        # must bear the secret nonce. A spoofed PRESENT line (e.g. inside an error
        # message that an attacker could influence) cannot carry the nonce.
        if nonce not in name:
            return None
        if name in rows:          # B2: a name may appear at most once
            return None
        axioms = tuple(a for a in axs.split(",") if a)
        if status == "MISSING":
            rows[name] = GoalResult(name, Verdict.NOT_PROVEN, (), "missing from environment")
        elif set(axioms) <= ALLOWED_AXIOMS:          # B7: axioms ⊆ {propext,Classical.choice,Quot.sound}
            rows[name] = GoalResult(name, Verdict.PROVEN, axioms)
        else:
            rows[name] = GoalResult(name, Verdict.NOT_PROVEN, axioms, "disallowed axioms")
    if set(rows) != set(expected):   # B2: exactly the expected names, no extras/missing
        return None
    return rows


def _run_once(goals: Sequence[Goal], header: str, runner: Runner, timeout: float):
    nonce = secrets.token_hex(16)
    r = render_batch(header, goals, nonce)
    try:
        _rc, out = runner(r.source, timeout)  # rc ignored on purpose: failing goals make it nonzero
    except subprocess.TimeoutExpired:
        return None, "timeout"
    rows = parse_summary(out, nonce, r.expected)
    if rows is None:
        return None, "no trustworthy summary"
    # B4: EVERY canary must read as expected, else the whole batch is untrusted.
    for cname, want in r.canary_expected.items():
        if rows[cname].verdict is not want:
            return None, f"canary {cname} misread: got {rows[cname].verdict.value}, want {want.value}"
    return {ext: rows[iname] for iname, ext in r.name_map.items()}, ""


def verify(goals: Sequence[Goal], header: str, runner: Runner,
           timeout: float = 600.0, max_batch: int = 400) -> dict[str, GoalResult]:
    """Verify goals in batches of at most max_batch, fail-closed, splitting on distrust."""
    results: dict[str, GoalResult] = {}

    def solve(chunk: Sequence[Goal]) -> None:
        got, why = _run_once(chunk, header, runner, timeout)
        if got is not None:
            results.update(got)
            return
        if len(chunk) == 1:
            g = chunk[0]
            results[g.name] = GoalResult(g.name, Verdict.UNKNOWN, (), why)
            return
        mid = len(chunk) // 2
        solve(chunk[:mid])
        solve(chunk[mid:])

    goals = list(goals)
    for i in range(0, len(goals), max_batch):
        solve(goals[i:i + max_batch])
    return results


def _timed_group_run(argv: Sequence[str], cwd: str, timeout: float,
                     grace: float = 5.0) -> tuple[int, str]:
    """Run ``argv`` in its OWN process session and, on timeout, kill the WHOLE group.

    v1.4.7 STEP 1: ``subprocess.run(timeout=...)`` kills only the direct child (``lake``);
    the orphaned ``lean`` grandchild keeps the stdout pipe open, so ``communicate()``
    blocks forever (the v1.4.6 hang).  Here the child gets ``start_new_session=True`` so
    ``lake`` and its ``lean`` grandchild share a new process group; on timeout we send
    SIGTERM to the group, wait a short grace, then SIGKILL, and drain the pipes.  A
    timeout returns a non-summary output so ``verify()`` maps the batch to UNKNOWN
    (fail-closed)."""
    proc = subprocess.Popen(list(argv), cwd=cwd, stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE, text=True, start_new_session=True)
    try:
        out, err = proc.communicate(timeout=timeout)
        return proc.returncode, (out or "") + "\n" + (err or "")
    except subprocess.TimeoutExpired:
        try:
            pgid = os.getpgid(proc.pid)
        except ProcessLookupError:
            pgid = None
        if pgid is not None:
            try:
                os.killpg(pgid, signal.SIGTERM)
            except ProcessLookupError:
                pass
        try:
            out, err = proc.communicate(timeout=grace)
        except subprocess.TimeoutExpired:
            if pgid is not None:
                try:
                    os.killpg(pgid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
            try:
                out, err = proc.communicate(timeout=grace)
            except subprocess.TimeoutExpired:
                out, err = "", ""
        return 124, "pf_trust: lake/lean exceeded timeout; process group killed (fail-closed)\n" + (err or "")
    finally:
        if proc.poll() is None:
            try:
                os.killpg(os.getpgid(proc.pid), signal.SIGKILL)
            except Exception:
                pass


def lake_runner(project_dir: str, extra_args: Iterable[str] = ()) -> Runner:
    """Runner that compiles a temporary file with `lake env lean` inside project_dir.

    extra_args are passed to `lean` before the file (e.g. a maxErrors option as
    defense in depth). Correctness does not depend on them.  On timeout the whole
    lake/lean process group is killed (see ``_timed_group_run``) and the temp file is
    always removed, so a slow/hung Lean cannot leak processes or files or block forever.
    """
    extra = list(extra_args)

    def run(source: str, timeout: float) -> tuple[int, str]:
        fd, path = tempfile.mkstemp(suffix=".lean", prefix="pf_batch_", dir=project_dir)
        try:
            with os.fdopen(fd, "w", encoding="utf-8") as f:
                f.write(source)
            return _timed_group_run(["lake", "env", "lean", *extra, path],
                                    cwd=project_dir, timeout=timeout)
        finally:
            try:
                os.remove(path)
            except FileNotFoundError:
                pass

    return run


def selftest(header: str, runner: Runner, n_false: int = 150) -> dict:
    """Reproduce the maxErrors scenario against the REAL toolchain.

    n_false unprovable goals, then interleaved provable/unprovable goals after
    them. Every goal must be classified correctly in a single trusted batch.
    """
    goals = [Goal(f"st_false_{i}", f"({i + 1} : Int) ≤ 0", "omega") for i in range(n_false)]
    tail = []
    for i in range(10):
        tail.append(Goal(f"st_tail_true_{i}", f"({i} : Int) ≤ {i + 1}", "omega"))
        tail.append(Goal(f"st_tail_false_{i}", f"({i + 1} : Int) ≤ {i}", "omega"))
    goals += tail
    expected = {g.name: (Verdict.PROVEN if "_true_" in g.name else Verdict.NOT_PROVEN) for g in goals}
    got, why = _run_once(goals, header, runner, timeout=1800.0)
    if got is None:
        return {"ok": False, "reason": f"single batch not trusted: {why}"}
    wrong = [n for n, v in expected.items() if got[n].verdict is not v]
    return {"ok": not wrong, "misclassified": wrong, "n_goals": len(goals)}


PF_DECISION_MODULE = True  # v1.5: hashed into the omega verdict cache key (pf_trust/cachekey.py)
