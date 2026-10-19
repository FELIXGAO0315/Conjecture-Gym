"""Content-addressed cache key for omega verdicts (v1.5 review, Priority A').

The v1.5 cold cache keyed on `git rev-parse HEAD`. That is BOTH too broad (any
unrelated commit invalidates the whole cache) and — more dangerously — says nothing
about WHAT code produced a verdict: a decision-logic change that is not committed, or
a toolchain bump, could let a stale PROVEN be silently reused. That is the single
easiest place to manufacture a false positive.

This module keys instead on a CONTENT fingerprint of everything that can change an
omega verdict:
  * the source of every DECISION module, discovered by STATIC import-closure from a
    small set of roots (NOT a hand-maintained file list — a manual list is itself a
    false-positive risk: miss one module and stale verdicts leak);
  * the Lean summary template + the ALLOWED_AXIOMS set (embedded in lean_batch, so
    already covered as file content, but also hashed explicitly for clarity);
  * the pinned toolchain / Mathlib / solver versions (pf_trust.pins);
  * an explicit ENCODING_VERSION bump knob.

A module is a DECISION module iff it sets `PF_DECISION_MODULE = True` at top level.
`check_coverage()` asserts every such tagged module in the repo is inside the closure
(so adding a new decision module that the roots don't reach FAILS loudly, rather than
silently leaving it out of the key).
"""
from __future__ import annotations

import ast
import hashlib
import importlib.util
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
ENCODING_VERSION = "v1.5"

# Roots of the decision-logic import closure. Everything that affects an omega/z3
# verdict must be reachable (by project-local import) from one of these.
_ROOTS = [
    "pf_trust.lean_batch",
    "pf_trust.props",
    "pf_trust.canon",
    "pf_trust.certify",
    "pf_trust.policies",
    "PolyForge.env.closure_complete",
]


def _module_file(modname: str) -> Path | None:
    try:
        spec = importlib.util.find_spec(modname)
    except (ModuleNotFoundError, ValueError, ImportError):
        return None
    if spec is None or not spec.origin or spec.origin == "built-in":
        return None
    p = Path(spec.origin)
    try:
        p.relative_to(ROOT)       # project-local only
    except ValueError:
        return None
    return p


def _imports_of(path: Path) -> set[str]:
    """Project-local module names imported by `path` (static AST, no execution)."""
    out: set[str] = set()
    tree = ast.parse(path.read_text(), filename=str(path))
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            for a in node.names:
                out.add(a.name)
        elif isinstance(node, ast.ImportFrom):
            if node.level == 0 and node.module:
                out.add(node.module)
                for a in node.names:                 # from pkg import submodule
                    out.add(f"{node.module}.{a.name}")
    return {m for m in out if m.split(".")[0] in ("pf_trust", "PolyForge")}


def import_closure(roots: list[str] | None = None) -> dict[str, Path]:
    """BFS the project-local import closure from the roots. Returns {modname: file}."""
    seen: dict[str, Path] = {}
    queue = list(roots or _ROOTS)
    while queue:
        m = queue.pop()
        if m in seen:
            continue
        f = _module_file(m)
        if f is None:
            continue
        seen[m] = f
        queue.extend(_imports_of(f) - seen.keys())
    return seen


def declared_decision_modules() -> dict[str, Path]:
    """Every repo module that tags itself `PF_DECISION_MODULE = True` (static scan)."""
    out: dict[str, Path] = {}
    for pkg in ("pf_trust", "PolyForge"):
        for f in (ROOT / pkg).rglob("*.py"):
            if "/.lake/" in str(f) or "/tests/" in str(f):
                continue
            try:
                tree = ast.parse(f.read_text(), filename=str(f))
            except (SyntaxError, UnicodeDecodeError):
                continue
            for node in tree.body:
                if (isinstance(node, ast.Assign)
                        and any(isinstance(t, ast.Name) and t.id == "PF_DECISION_MODULE" for t in node.targets)
                        and isinstance(node.value, ast.Constant) and node.value.value is True):
                    rel = f.relative_to(ROOT)
                    out[str(rel).replace("/", ".")[:-3]] = f
    return out


def check_coverage() -> list[str]:
    """Return tagged decision modules NOT in the import closure (empty == covered)."""
    closure_files = {p.resolve() for p in import_closure().values()}
    missing = []
    for mod, f in declared_decision_modules().items():
        if f.resolve() not in closure_files:
            missing.append(mod)
    return sorted(missing)


def verdict_fingerprint() -> str:
    """sha256 over: ENCODING_VERSION + sorted (relpath, sha256(content)) of every
    module in the decision closure + the pinned versions. Stable across unrelated
    commits; changes iff decision code or the toolchain/solver pins change."""
    from pf_trust import pins
    h = hashlib.sha256()
    h.update(("ENCODING_VERSION=" + ENCODING_VERSION + "\n").encode())
    for mod, f in sorted(import_closure().items()):
        rel = str(f.relative_to(ROOT))
        digest = hashlib.sha256(f.read_bytes()).hexdigest()
        h.update(f"{rel}={digest}\n".encode())
    v = pins.versions()
    for k in ("lean_toolchain", "mathlib_rev", "z3-solver", "graphcalc", "python_mm"):
        h.update(f"pin:{k}={v.get(k)}\n".encode())
    return h.hexdigest()


if __name__ == "__main__":
    import json
    miss = check_coverage()
    print(json.dumps({
        "verdict_fingerprint": verdict_fingerprint(),
        "closure_modules": sorted(import_closure()),
        "declared_decision_modules": sorted(declared_decision_modules()),
        "coverage_missing": miss,
    }, indent=2))
    raise SystemExit(1 if miss else 0)
