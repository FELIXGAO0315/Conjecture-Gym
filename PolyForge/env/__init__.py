"""PolyForge verification environment.

The Lean-verification toolkit the graph pipeline relies on: a stable task format
(:mod:`tasks`), a fast batched Lean verifier with layered anti-cheating checks
(:mod:`verifier`), the fail-closed closure/soundness helpers (:mod:`closure_complete`),
and the discard / replace gates (:mod:`discardlog`, :mod:`replace_gate`).  Audit
harnesses live in :mod:`analysis`.
"""

ENV_VERSION = "2.0"
