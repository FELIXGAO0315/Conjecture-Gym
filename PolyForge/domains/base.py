"""The PolyForge domain interface.

A *domain* supplies everything the generic engine (``anvil``), generation driver
(``generator``), formalizer-compilation layer (``formalizer``) and scoring
(``scoring``) need in order to mine, prove, score and record conjectures for one
mathematical subject.  The common code accesses a domain ONLY through this
interface, so it never names anything domain-specific.

A domain provides the following (the hex domain, ``domains.hex``, implements all
of them; the graph domain is so far a skeleton):

Identity & locations
    name                 short domain name ("hex", "graph")
    record_dir           Path to the record/ directory
    lean_dir             Path to the domain's Lean project
    data_path            Path to the domain's dataset
    generator_version    version stamped into new records (shared "1.0")

Deduction-engine configuration (consumed by ``anvil.deducer.configure``)
    inventory            module with INVENTORY / INVENTORY_BY_NAME /
                         CONDITIONAL_THEOREMS / ALL_VARS / PROP_VARS / NONNEG_VARS
    base_directions      directed objectives explored each saturation round
    split_specs          conditional-theorem case-split expressions + thresholds
    bnb_vars             branch-and-bound split variables
    group_work_budget    per-premise-set LP/MILP solve budget
    ro_max_ratio         supplement-phase cap ratio

Run setup
    ensure_lean_fresh()                         rebuild stale domain Lean lemmas
    load_pool()                                 -> dataset pool object
    load_existing_hashes()                      -> (hashes, max_id)
    build_skeleton_index(features)              -> skeleton -> best-record info
    select_lemma_library()                      -> (lemmas, lemma_meta, lemma_data)
    vars_from_pvec(obj)                          exact variable valuation of an object
    set_run_context(pool, hashes_snapshot, base_seed, lemmas, lemma_meta)

Per-premise-set pipeline (worker side)
    process_premise_set(rng, stats, seed, accept) -> proposal | None

Record assembly / judging (main side)
    assemble_data(proposal, name, supersedes)   -> record data dict
    skeleton_better(new_metrics, old_metrics)    -> bool

Formalizer
    build_theorem(name, premises, conclusion, steps, display)   -> str
    build_record_lean(name, premises, conclusion, steps, lemma_data) -> str
    lemma_cnums_in(steps)                        -> set of lemma C-numbers
    lemma_defs_block(cnums, lemma_data)          -> str (shared batch preamble)
    compile_batch(entries, preamble)             -> (results, meta)
    compile_lean(name, source)                   -> (ok, message)
"""

from __future__ import annotations

from abc import ABC, abstractmethod


class Domain(ABC):
    """Abstract base documenting the contract above.  Attributes are set by the
    concrete domain (usually in ``__init__`` / at import); the methods below are
    the behavioural part of the interface."""

    name: str = ""

    # ── run setup ─────────────────────────────────────────────────────────────
    @abstractmethod
    def ensure_lean_fresh(self):
        ...

    @abstractmethod
    def load_pool(self):
        ...

    @abstractmethod
    def load_existing_hashes(self):
        ...

    @abstractmethod
    def build_skeleton_index(self, features):
        ...

    @abstractmethod
    def select_lemma_library(self):
        ...

    @abstractmethod
    def vars_from_pvec(self, obj):
        ...

    @abstractmethod
    def set_run_context(self, pool, hashes_snapshot, base_seed, lemmas, lemma_meta):
        ...

    # ── per-premise-set pipeline ───────────────────────────────────────────────
    @abstractmethod
    def process_premise_set(self, rng, stats, seed, accept):
        ...

    # ── record assembly / judging ──────────────────────────────────────────────
    @abstractmethod
    def assemble_data(self, proposal, name, supersedes):
        ...

    @abstractmethod
    def skeleton_better(self, new_metrics, old_metrics):
        ...

    # ── formalizer ─────────────────────────────────────────────────────────────
    @abstractmethod
    def build_theorem(self, name, premises, conclusion, steps, display=True):
        ...

    @abstractmethod
    def build_record_lean(self, name, premises, conclusion, steps, lemma_data):
        ...

    @abstractmethod
    def lemma_cnums_in(self, steps):
        ...

    @abstractmethod
    def lemma_defs_block(self, cnums, lemma_data):
        ...

    @abstractmethod
    def compile_batch(self, entries, preamble=""):
        ...

    @abstractmethod
    def compile_lean(self, name, source):
        ...
