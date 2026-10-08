"""The graph domain (PolyForge v1.1, stage 1): linear inventory over graph
invariants, wired to the generic engine behind the Domain interface.  All
behaviour for conjecture mining lives in the graph submodules; this class wires
them together.
"""

from __future__ import annotations

import subprocess
from pathlib import Path

from ...anvil import deducer as D
from ...generator import generator as CG
from ..base import Domain
from . import deduction as DED
from . import formalizer as F
from . import generator as G


class GraphDomain(Domain):
    name = "graph"

    def __init__(self):
        self.record_dir = G.RECORD
        self.lean_dir = F.LEAN_DIR
        self.data_path = G.DATA
        self.generator_version = G.GENERATOR_VERSION
        # engine configuration (INVENTORY rebuilt per premise set by DED)
        self.inventory = DED
        self.base_directions = DED.BASE_DIRECTIONS
        self.split_specs = DED.SPLIT_SPECS
        self.bnb_vars = DED.BNB_VARS
        self.group_work_budget = G.GROUP_WORK_BUDGET
        self.ro_max_ratio = G.RO_MAX_RATIO
        self.pool = None
        self.hashes = None
        self.base_seed = None

    # ── run setup ─────────────────────────────────────────────────────────────
    def ensure_lean_fresh(self):
        src = self.lean_dir / "GraphLemmas.lean"
        olean = self.lean_dir / ".lake" / "build" / "lib" / "lean" / "GraphLemmas.olean"
        if olean.exists() and olean.stat().st_mtime >= src.stat().st_mtime:
            return "up-to-date"
        print("  GraphLemmas.lean changed — running `lake build GraphLemmas` ...")
        res = subprocess.run(["lake", "build", "GraphLemmas"], cwd=str(self.lean_dir),
                             capture_output=True, text=True)
        out = (res.stdout + res.stderr).strip()
        if res.returncode != 0 or "error:" in out:
            raise RuntimeError("lake build GraphLemmas failed:\n" + out[:4000])
        return "rebuilt"

    def load_pool(self):
        return G.load_pool()

    def load_existing_hashes(self):
        return G.load_existing_hashes(self.record_dir)

    def build_skeleton_index(self, features):
        return G.build_skeleton_index(self.record_dir, features)

    def select_lemma_library(self):
        return G.select_lemma_library(self.record_dir)

    def vars_from_pvec(self, obj):
        return DED.vars_from_graph(obj)

    def set_run_context(self, pool, hashes_snapshot, base_seed, lemmas, lemma_meta):
        self.pool = pool[0] if isinstance(pool, tuple) else pool
        self.hashes = hashes_snapshot
        self.base_seed = base_seed
        D.configure(self)
        D.set_lemmas(lemmas or {})
        G.set_lemma_meta(lemma_meta)
        CG.set_domain(self)

    # ── per-premise-set pipeline ───────────────────────────────────────────────
    def process_premise_set(self, rng, stats, seed, accept):
        return G.process_premise_set(rng, self.pool, self.hashes, stats, seed, accept)

    # ── record assembly / judging ──────────────────────────────────────────────
    def assemble_data(self, proposal, name, supersedes):
        return G.assemble_data(proposal, name, supersedes)

    def skeleton_better(self, new_metrics, old_metrics):
        return G.skeleton_better(new_metrics, old_metrics)

    # ── formalizer ─────────────────────────────────────────────────────────────
    def build_theorem(self, name, premises, conclusion, steps, display=True):
        return F.build_theorem(name, premises, conclusion, steps, display=display)

    def build_record_lean(self, name, premises, conclusion, steps, lemma_data):
        return F.build_record_lean(name, premises, conclusion, steps, lemma_data)

    def lemma_cnums_in(self, steps):
        return F._lemma_cnums_in(steps)

    def lemma_defs_block(self, cnums, lemma_data):
        return F.lemma_defs_block(cnums, lemma_data)

    def compile_batch(self, entries, preamble=""):
        return F.compile_batch(entries, preamble=preamble)

    def compile_lean(self, name, source):
        return F.compile_lean(name, source)
