"""PolyForge core training environment (v1.3).

Turns the PolyForge record of true, Lean-verified conjectures into a reusable RL
environment: a stable task format (:mod:`tasks`), a fast batched Lean verifier
with layered anti-cheating checks (:mod:`verifier`), an RL reward function
(:mod:`reward`), a pass@k evaluator (:mod:`evaluate`), and a dataset exporter with
a skeleton-based train/test split (:mod:`export`).

The tooling is domain-agnostic; v1.3 wires up the ``graph`` domain only (the
``hex`` domain relies on an Inventory with ``sorry``-as-axiom placeholders, which
cannot pass the standard-axioms check).
"""

ENV_VERSION = "1.3"
