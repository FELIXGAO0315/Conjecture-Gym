"""The hex domain (p₆ of simple 3-polytopes) — the original HexForge subject,
re-expressed behind the PolyForge :class:`Domain` interface.  All behaviour is
unchanged; this class just wires the hex submodules to the generic engine.
"""

from __future__ import annotations

from ...engine import deducer as D
from ...engine import generator as CG
from ..base import Domain
from . import inventory as INV
from . import deduction as DED
from . import iris as IRIS
from . import formalizer as F
from . import generator as G


class HexDomain(Domain):
    name = "hex"

    def __init__(self):
        # identity & locations
        self.record_dir = G.RECORD
        self.lean_dir = F.LEAN_DIR
        self.data_path = G.DATA
        self.generator_version = CG.GENERATOR_VERSION
        # deduction-engine configuration
        self.inventory = INV
        self.base_directions = DED.BASE_DIRECTIONS
        self.split_specs = DED.SPLIT_SPECS
        self.bnb_vars = DED.BNB_VARS
        self.group_work_budget = G.GROUP_WORK_BUDGET
        self.ro_max_ratio = CG.RO_MAX_RATIO
        self.feature_vars = IRIS.FEATURES
        # run context (populated by set_run_context)
        self.pool = None
        self.hashes = None
        self.base_seed = None

    # ── run setup ─────────────────────────────────────────────────────────────
    def ensure_lean_fresh(self):
        return F.ensure_hexlemmas_fresh()

    def load_pool(self):
        pvecs, features = G.load_pool()
        pvec_vars = [DED.vars_from_pvec(pv) for pv in pvecs]
        return (pvecs, features, pvec_vars)

    def load_existing_hashes(self):
        return G.load_existing_hashes(self.record_dir)

    def build_skeleton_index(self, features):
        return G.build_skeleton_index(self.record_dir, features)

    def select_lemma_library(self):
        return G.select_lemma_library(self.record_dir)

    def vars_from_pvec(self, obj):
        return DED.vars_from_pvec(obj)

    def set_run_context(self, pool, hashes_snapshot, base_seed, lemmas, lemma_meta):
        self.pool = pool
        self.hashes = hashes_snapshot
        self.base_seed = base_seed
        D.configure(self)                 # wire the engine to this domain
        D.set_lemmas(lemmas or {})        # workers (forked after this) inherit the library
        G.set_lemma_meta(lemma_meta)      # lemma metadata for generation/cost
        CG.set_domain(self)               # the worker entry point dispatches here

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
