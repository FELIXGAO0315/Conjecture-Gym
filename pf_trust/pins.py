"""Version pinning + a startup assertion that refuses to run on version drift.

Why this exists (v1.5 PHASE A)
------------------------------
Every MEASURED number must be reproducible.  A silent toolchain / dependency
bump would invalidate the omega verdicts and the baselines without anyone
noticing.  ``assert_pins()`` is called at the top of every long job and every
analysis script; it fails LOUD (raises) on any drift from the declared pins, and
``versions()`` returns the actual environment so it can be stamped into every
artifact.

The declared pins live in ``analysis/v1.5/pins.json`` (machine-readable, the
single source of truth).  The Lean toolchain and the Mathlib revision are pinned
by files already tracked in the repo (``lean/lean-toolchain``,
``lean/lake-manifest.json``); here we assert those files still equal the declared
values, so an accidental edit is caught without needing to spawn ``lake``.
"""
from __future__ import annotations

import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
PINS_FILE = ROOT / "analysis" / "v1.5" / "pins.json"
LEAN_DIR = ROOT / "PolyForge" / "domains" / "graph" / "lean"
TOOLCHAIN_FILE = LEAN_DIR / "lean-toolchain"
MANIFEST_FILE = LEAN_DIR / "lake-manifest.json"


class PinDrift(RuntimeError):
    """Raised when the live environment does not match the declared pins."""


def _pkg_version(name: str) -> str | None:
    try:
        if name == "z3-solver":
            import z3
            return z3.get_version_string()
        if name == "graphcalc":
            import graphcalc
            return graphcalc.__version__
        if name == "pytest":
            import pytest
            return pytest.__version__
    except Exception:
        return None
    return None


def _mathlib_rev() -> str | None:
    try:
        m = json.loads(MANIFEST_FILE.read_text())
        for p in m.get("packages", []):
            if p.get("name") == "mathlib":
                return p.get("rev")
    except Exception:
        return None
    return None


def _python_mm() -> str:
    import sys
    return f"{sys.version_info.major}.{sys.version_info.minor}"


def versions() -> dict:
    """The ACTUAL environment, for stamping into every artifact."""
    import sys
    return {
        "python": sys.version.split()[0],
        "python_mm": _python_mm(),
        "graphcalc": _pkg_version("graphcalc"),
        "pytest": _pkg_version("pytest"),
        "z3-solver": _pkg_version("z3-solver"),
        "lean_toolchain": (TOOLCHAIN_FILE.read_text().strip()
                           if TOOLCHAIN_FILE.exists() else None),
        "mathlib_rev": _mathlib_rev(),
    }


def declared() -> dict:
    return json.loads(PINS_FILE.read_text())


def diff() -> list[str]:
    """Return a list of human-readable drift messages (empty == OK)."""
    exp = declared()["expected"]
    act = versions()
    out: list[str] = []
    # python: compare major.minor only (patch may float)
    if act["python_mm"] != exp["python_mm"]:
        out.append(f"python: expected {exp['python_mm']}.x, got {act['python']}")
    for key in ("graphcalc", "pytest", "z3-solver", "lean_toolchain", "mathlib_rev"):
        if act.get(key) != exp.get(key):
            out.append(f"{key}: expected {exp.get(key)!r}, got {act.get(key)!r}")
    return out


def assert_pins() -> dict:
    """Refuse to run on drift.  Returns ``versions()`` on success."""
    drift = diff()
    if drift:
        raise PinDrift("version drift detected (refusing to run):\n  " +
                       "\n  ".join(drift))
    return versions()


if __name__ == "__main__":
    import sys
    if "--write-expected" in sys.argv:
        # One-off: initialise pins.json from the current environment.
        PINS_FILE.parent.mkdir(parents=True, exist_ok=True)
        v = versions()
        expected = {k: v[k] for k in
                    ("python_mm", "graphcalc", "pytest", "z3-solver",
                     "lean_toolchain", "mathlib_rev")}
        PINS_FILE.write_text(json.dumps(
            {"note": "declared pins for PolyForge v1.5; assert_pins() refuses to "
                     "run on drift. python compared at major.minor.",
             "expected": expected}, indent=2) + "\n")
        print("wrote", PINS_FILE)
    else:
        print(json.dumps({"actual": versions(), "drift": diff()}, indent=2))
        sys.exit(1 if diff() else 0)
