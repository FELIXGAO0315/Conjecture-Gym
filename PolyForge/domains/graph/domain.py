"""The graph domain — skeleton (PolyForge v1.0).

The graph domain's Lean project (recent Mathlib, pinned to v4.34.0) and dataset
(``data/graph_pool.json``) exist, but the graph *Inventory* (the proved base of
graph theorems that the deduction engine reasons over) has not yet been wired
up.  Until it is, ``python -m run polyforge graph`` prints a notice and exits;
no graph conjectures are generated in this version.
"""

from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parent             # domains/graph/
LEAN_DIR = ROOT / "lean"
DATA = ROOT / "data" / "graph_pool.json"


class GraphDomain:
    """Placeholder domain.  ``ready`` is False until the graph Inventory is wired
    in; the driver checks this and exits early with ``notice``."""

    name = "graph"
    ready = False
    notice = "graph 领域尚未接入 Inventory"

    def __init__(self):
        self.record_dir = ROOT / "record"
        self.lean_dir = LEAN_DIR
        self.data_path = DATA
