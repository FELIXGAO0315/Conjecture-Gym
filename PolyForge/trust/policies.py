"""Decision policies that keep pruning sound when a checker is uncertain.

Rule of thumb used everywhere: a wrong "entailed" deletes a true theorem
(unsound); a wrong "not entailed" only keeps a redundant one (incomplete). So
uncertainty and floating-point answers may only ever push toward "not entailed".
"""
from __future__ import annotations

from enum import Enum
from typing import Callable

from .lean_batch import Verdict


class Ent(str, Enum):
    ENTAILED = "entailed"
    NOT_ENTAILED = "not_entailed"
    UNKNOWN = "unknown"


def from_lean(v: Verdict) -> Ent:
    return {Verdict.PROVEN: Ent.ENTAILED,
            Verdict.NOT_PROVEN: Ent.NOT_ENTAILED,
            Verdict.UNKNOWN: Ent.UNKNOWN}[v]


def decide_with_prefilter(pair, float_says_not_entailed: Callable[[object], bool],
                          exact_decide: Callable[[object], Ent]) -> Ent:
    """A floating-point solver (e.g. PuLP/CBC) may only short-cut to NOT_ENTAILED.
    Any ENTAILED must come from the exact decider (omega via lean_batch)."""
    if float_says_not_entailed(pair):
        return Ent.NOT_ENTAILED
    return exact_decide(pair)


def may_prune(result: Ent) -> bool:
    """Only an exact, positively confirmed entailment may delete a record."""
    return result is Ent.ENTAILED


def may_replace(old, new, usable: Callable[[object, object], bool],
                entails_by: Callable[[object, list], Ent]) -> bool:
    """`new` may replace `old` only if `old` is entailed by `new` alone:
    new is usable for old (old's premises imply new's premises, param-aware), and
    old's conclusion follows from old's premises + inventory + new's conclusion.
    Otherwise both are kept."""
    if not usable(old, new):
        return False
    return may_prune(entails_by(old, [new]))


