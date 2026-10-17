"""Checker-independent audits.

Both audits take the project's own functions as arguments, so they test the
project's real code rather than a re-implementation.
"""
from __future__ import annotations

from typing import Callable, Iterable


def monotonicity_violations(pairs: Iterable[tuple[object, object]],
                            restricted_usable: Callable[[object, object], bool],
                            complete_usable: Callable[[object, object], bool]) -> list:
    """The complete check must accept everything the (sound) restricted check accepts.
    A violation means one of the two is wrong: either restricted accepted an unsound
    pair, or complete rejected a valid one (false negative)."""
    out = []
    for t, r in pairs:
        if restricted_usable(t, r) and not complete_usable(t, r):
            out.append((t, r))
    return out


def graph_soundness_violations(pairs: Iterable[tuple[object, object]],
                               judged_usable: Callable[[object, object], bool],
                               graphs: Iterable[object],
                               satisfies_premises: Callable[[object, object], bool]) -> list:
    """For every pair judged usable, no graph may satisfy T's premises while
    violating R's premises. Returns (T, R, graph) witnesses of unsoundness."""
    graphs = list(graphs)
    out = []
    for t, r in pairs:
        if not judged_usable(t, r):
            continue
        for g in graphs:
            if satisfies_premises(t, g) and not satisfies_premises(r, g):
                out.append((t, r, g))
                break
    return out
