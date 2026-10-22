"""Lean 4 compilation machinery (domain-agnostic).

The domain-specific translation of a deduction proof into a Lean theorem lives
in the domain (e.g. ``domains.hex.formalizer``); this module only knows how to
*compile* Lean sources: run ``lake env lean`` on a single source, or on a whole
batch of header-less theorem bodies sharing one import header (so Mathlib is
elaborated once per batch), bisecting a failed batch to locate the offenders.

A source is accepted only when it compiles cleanly AND contains no banned token
(``sorry`` / ``admit`` / ``axiom`` / ``native_decide``) — spec §2 / §III.4.
"""

from __future__ import annotations

import subprocess
import re as _re


def _check_source(returncode, out, source):
    """Shared success criteria: return code 0, no ``error:``, no
    ``declaration uses 'sorry'`` warning, and no banned token in the source
    itself.  Returns ``(ok, reason_str)``."""
    banned = [w for w in ("sorry", "admit", "axiom", "native_decide")
              if _re.search(r"\b" + w + r"\b", source)]
    reasons = []
    if returncode != 0:
        reasons.append(f"return code {returncode}")
    if "error:" in out:
        reasons.append("error: in output")
    if "declaration uses 'sorry'" in out:
        reasons.append("declaration uses 'sorry'")
    if banned:
        reasons.append("banned tokens in source: " + ",".join(banned))
    return (not reasons), "; ".join(reasons)


def _run_lean(stem: str, source: str, lean_dir, timeout: int):
    """Write ``{stem}.lean`` in ``lean_dir``, run ``lake env lean`` on it, and
    delete it.  Returns ``(ok, message)``."""
    target = lean_dir / f"{stem}.lean"
    target.write_text(source)
    try:
        res = subprocess.run(
            ["lake", "env", "lean", str(target)],
            cwd=str(lean_dir), capture_output=True, text=True, timeout=timeout,
        )
    except subprocess.TimeoutExpired:
        target.unlink(missing_ok=True)
        return False, "compile timeout"
    out = (res.stdout + res.stderr).strip()
    ok, reason = _check_source(res.returncode, out, source)
    target.unlink(missing_ok=True)
    if ok:
        return True, "ok"
    return False, (reason + " || " + out)[:2000]


def compile_lean(name: str, source: str, lean_dir, timeout: int = 300) -> tuple:
    """Compile a single full (header + theorem) source.  Used for standalone
    record verification (checkpoint §9.5) and single-conjecture fallbacks."""
    return _run_lean(name, source, lean_dir, timeout)


def compile_batch(entries: list, lean_dir, header: str, timeout: int = 300,
                  preamble: str = "", stem_prefix: str = "_Batch_"):
    """v0.6.4 §III: compile many theorems in ONE file (Mathlib loaded once).

    ``entries`` is a list of ``(name, theorem_src)`` with header-less theorem
    bodies and unique names.  ``header`` is the shared import header; ``preamble``
    (v0.7 §5) is a shared block of inlined lemma definitions placed once after the
    header, so lemma-using theorems can reference them.  On a whole-batch failure
    the batch is bisected to locate the offender(s); only the failing theorems are
    reported failed.

    Returns ``(results, meta)`` where ``results`` maps name -> bool (compiled)
    and ``meta`` is ``{"bisections": k}`` (number of extra sub-compiles beyond
    the initial whole-batch attempt)."""
    results = {}
    meta = {"bisections": 0}
    pre = (preamble + "\n\n") if preamble else ""

    def src_of(subset):
        return header + pre + "\n\n".join(t for _n, t in subset) + "\n"

    def stem_of(subset):
        return stem_prefix + "_".join(n for n, _t in subset[:1]) + f"_{len(subset)}"

    def recurse(subset, is_top):
        if not subset:
            return
        ok, _msg = _run_lean(stem_of(subset), src_of(subset), lean_dir, timeout)
        if not is_top:
            meta["bisections"] += 1
        if ok:
            for n, _t in subset:
                results[n] = True
            return
        if len(subset) == 1:
            results[subset[0][0]] = False
            return
        mid = len(subset) // 2
        recurse(subset[:mid], False)
        recurse(subset[mid:], False)

    recurse(list(entries), True)
    return results, meta
