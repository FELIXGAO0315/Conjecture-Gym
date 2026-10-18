"""The single fail-closed gate for an in-place record replacement (v1.5 PHASE D).

Kept in its own importable module (not inside run.py) so the decision is unit-testable
without run.py's entry-point side effects.
"""
from __future__ import annotations

from . import discardlog


def replace_decision(domain, old_name, tentative) -> bool:
    """Return True iff the new record alone entails the old (domain.may_replace).

    A missing may_replace defaults to allow (legacy behaviour). NOT_ENTAILED / UNKNOWN
    (via policies.may_replace) or ANY exception inside may_replace -> False (KEEP BOTH):
    a wrong True would delete a true theorem, so uncertainty must never replace."""
    _may = getattr(domain, "may_replace", None)
    if _may is None:
        # Legacy domains (e.g. hex) have no entailment-checked replacement; preserve the
        # historical allow so hex behaviour is unchanged (HARD CONSTRAINT: do not touch
        # hex). v1.5 audit: make this latent path OBSERVABLE rather than silent.
        discardlog.record("replace", "no_may_replace_legacy_allow", {"old": old_name})
        return True
    try:
        return bool(_may(old_name, tentative))
    except Exception:
        discardlog.record("replace", "may_replace_crash_keep_both", {"old": old_name})
        return False
