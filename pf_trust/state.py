"""Machine-readable resumability state for PolyForge v1.5 (R3).

``analysis/v1.5/state.json`` records, per phase: status, the commit that
completed it, and the artifacts it produced. On start, ``first_incomplete()``
tells the driver which phase to resume from. JSON only (never markdown).
"""
from __future__ import annotations

import json
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
STATE_FILE = ROOT / "analysis" / "v1.5" / "state.json"

PHASES = ["A", "B", "R2", "C", "D", "E", "F", "G", "H", "I"]


def _head() -> str:
    try:
        return subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT,
                                       text=True).strip()
    except Exception:
        return ""


def load() -> dict:
    if STATE_FILE.exists():
        return json.loads(STATE_FILE.read_text())
    return {"version": "v1.5", "phases": {p: {"status": "pending"} for p in PHASES}}


def save(state: dict) -> None:
    STATE_FILE.parent.mkdir(parents=True, exist_ok=True)
    state["head_commit"] = _head()
    STATE_FILE.write_text(json.dumps(state, indent=2) + "\n")


def mark(phase: str, status: str, commit: str | None = None,
         artifacts: list | None = None, notes: str | None = None) -> dict:
    state = load()
    ph = state["phases"].setdefault(phase, {})
    ph["status"] = status
    if commit is not None:
        ph["commit"] = commit
    if artifacts is not None:
        ph["artifacts"] = artifacts
    if notes is not None:
        ph["notes"] = notes
    save(state)
    return state


def first_incomplete() -> str | None:
    state = load()
    for p in PHASES:
        if state["phases"].get(p, {}).get("status") != "complete":
            return p
    return None


if __name__ == "__main__":
    import sys
    if len(sys.argv) >= 3:
        mark(sys.argv[1], sys.argv[2],
             notes=sys.argv[3] if len(sys.argv) > 3 else None)
    print(json.dumps(load(), indent=2))
    print("first_incomplete:", first_incomplete())
