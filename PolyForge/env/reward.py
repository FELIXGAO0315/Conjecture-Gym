"""PolyForge RL reward function (v1.3 §IV).

A thin wrapper over the verifier suitable for TRL / verl and similar frameworks:
given parallel lists of ``task_ids`` and model ``completions``, return a list of
float rewards (1.0 for an accepted proof, 0.0 otherwise).

Proof-extraction rule (documented in the exported README):
  * take the content of the **last** ```` ```lean ```` fenced code block in the
    completion;
  * if that content begins with ``by`` (optionally after whitespace), drop the
    leading ``by`` — the verifier wraps the task's ``:= by`` already;
  * if there is no ```` ```lean ```` block, the reward is 0 with status
    ``no_proof_found``.
"""

from __future__ import annotations

import re

from .verifier import Verifier

_LEAN_BLOCK_RE = re.compile(r"```lean[^\n]*\n(.*?)```", re.DOTALL)
_LEADING_BY_RE = re.compile(r"\A\s*by\b[ \t]*\n?")


def extract_proof(completion: str) -> str | None:
    """Return the proof tactic block from a model completion, or ``None`` if no
    ```` ```lean ```` block is present."""
    blocks = _LEAN_BLOCK_RE.findall(completion)
    if not blocks:
        return None
    proof = blocks[-1]
    proof = _LEADING_BY_RE.sub("", proof, count=1)
    return proof.strip("\n")


_VERIFIER_CACHE: dict[tuple, Verifier] = {}


def _get_verifier(domain: str, nprocs: int, **kw) -> Verifier:
    key = (domain, nprocs, kw.get("max_heartbeats"), kw.get("timeout"))
    if key not in _VERIFIER_CACHE:
        _VERIFIER_CACHE[key] = Verifier(domain, nprocs=nprocs, **kw)
    return _VERIFIER_CACHE[key]


def reward_fn(task_ids, completions, domain: str = "graph", nprocs: int = 1,
              return_status: bool = False, verifier: Verifier | None = None, **verifier_kw):
    """Compute rewards for a batch of completions.

    ``task_ids`` and ``completions`` are parallel sequences.  Returns a list of
    floats; if ``return_status`` is true, returns ``(rewards, statuses)`` where
    ``statuses`` is a list of per-item verifier status strings (``no_proof_found``
    when the completion has no ```` ```lean ```` block)."""
    V = verifier or _get_verifier(domain, nprocs, **verifier_kw)
    items, slots = [], []
    rewards = [0.0] * len(task_ids)
    statuses = ["no_proof_found"] * len(task_ids)
    for i, (tid, comp) in enumerate(zip(task_ids, completions)):
        proof = extract_proof(comp or "")
        if proof is None:
            continue
        slots.append(i)
        items.append((tid, proof))
    if items:
        for slot, res in zip(slots, V.verify_batch(items)):
            rewards[slot] = res.reward
            statuses[slot] = res.status
    if return_status:
        return rewards, statuses
    return rewards
