"""Structured logging of EVERY discarded generation candidate (v1.5 PHASE D).

The published run archived only the discards that become pruned-archive entries
(reasons: redundant_vs_record, pruned_by_newer, replaced_by, pruned_basis_audit).
PRE-archive discards — same_skeleton_worse, lemma_protected, replace_blocked_kept_both,
always-true-premise rejections, name-only mismatches — were never persisted, so the
published data cannot witness them.

This module records every discard with its stage, reason and the decision inputs to a
structured JSONL, so a FUTURE run has a complete, machine-readable discard trace. It is
a NO-OP unless explicitly enabled (env PF_DISCARD_LOG=<path> or ``enable(path)``), so it
changes NOTHING about the generation decision or the published pipeline.
"""
from __future__ import annotations

import json
import os
import threading
from pathlib import Path

_lock = threading.Lock()
_path: Path | None = None
_mem: list[dict] = []           # in-memory mirror (used by tests)
_capture_mem = False


def enable(path: str | os.PathLike | None = None, capture_mem: bool = False) -> None:
    global _path, _capture_mem
    _path = Path(path) if path else None
    _capture_mem = capture_mem
    if _path:
        _path.parent.mkdir(parents=True, exist_ok=True)


def _enabled() -> bool:
    return _path is not None or _capture_mem or bool(os.environ.get("PF_DISCARD_LOG"))


def reset_mem() -> None:
    with _lock:
        _mem.clear()


def records() -> list[dict]:
    with _lock:
        return list(_mem)


def record(stage: str, reason: str, inputs: dict | None = None) -> None:
    """Log one discarded candidate. Safe to call always; no-op unless enabled."""
    if not _enabled():
        return
    entry = {"stage": stage, "reason": reason, "inputs": inputs or {}}
    with _lock:
        if _capture_mem:
            _mem.append(entry)
        p = _path or (Path(os.environ["PF_DISCARD_LOG"]) if os.environ.get("PF_DISCARD_LOG") else None)
        if p is not None:
            try:
                p.parent.mkdir(parents=True, exist_ok=True)
                with open(p, "a") as f:
                    f.write(json.dumps(entry) + "\n")
            except Exception:
                pass            # logging must never affect the pipeline
