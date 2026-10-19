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
        self.snapshot_records = G.load_records(self.record_dir)   # run-start snapshot (§V/§VI)
        G.set_snapshot_records(self.snapshot_records)
        D.configure(self)
        D.set_lemmas(lemmas or {})
        G.set_lemma_meta(lemma_meta)
        CG.set_domain(self)

    # ── main-process commit checks (§V re-check + §VI Dalmatian) ───────────────
    def main_commit_check(self, prop, committed):
        return G.main_commit_check(prop, committed, self.snapshot_records, self.pool)

    # ── v1.4 §I: reverse pruning (main process, commit order) ──────────────────
    def reverse_prune(self, new_data, segment=None, commit_index=None):
        """Drop every existing record made redundant by the just-committed
        ``new_data``.  Returns ``[(victim_id, used_ids), …]``.  Keeps the main-process
        snapshot (read by ``main_commit_check``) consistent with the on-disk record.
        Each prune is archived to record/pruned.jsonl (§D1)."""
        victims = G.apply_reverse_prune(self.record_dir, new_data, segment, commit_index)
        if victims:
            drop = {vid for vid, _ in victims}
            self.snapshot_records = [d for d in self.snapshot_records
                                     if d.get("id") not in drop]
        return victims

    def may_replace(self, old_id, new_data):
        """v1.4.6 §5.2: a new record may REPLACE an old one (same skeleton) only when the
        new record alone entails the old — via PolyForge.trust.policies.may_replace:
        (a) the new record is usable for the old (old's premises imply new's premises,
        PARAMETER-AWARE: G._premises_imply), and (b) the old's conclusion follows, by the
        COMPLETE check (omega via lean_batch), from old's premises + restricted inventory +
        the new's conclusion.  Otherwise both are kept.  A wrong True would delete a true
        theorem, so UNKNOWN maps to NOT_ENTAILED (keep both)."""
        import json as _json
        from PolyForge.trust import policies as POL
        from PolyForge.trust.lean_batch import Verdict
        from PolyForge.env import closure_complete as CC
        p = self.record_dir / old_id / f"{old_id}.json"
        if not p.exists():
            return True   # cannot find the old record on disk: fall back to legacy replace
        old = _json.loads(p.read_text())
        old_view = G._record_premise_view(old)
        new_view = G._record_premise_view(new_data)

        def usable(o, n):
            return G._premises_imply(o, n)   # old's premises imply new's (param-aware now)

        def entails_by(o, records):
            # old's canonical conclusion from old premises + inventory + the given records
            facts, goal, vs, _m = CC.collect_facts_complete(
                o["props"], o["numeric"], o["canon"], records)
            proven = CC.omega_decide_batch([("t", facts, goal, vs)])[0]["t"]
            return POL.from_lean(Verdict.PROVEN if proven else Verdict.NOT_PROVEN)

        return POL.may_replace(old_view, new_view, usable, entails_by)

    def archive_replacement(self, old_id, replacer_data, segment=None, commit_index=None):
        """§G1: archive the record being overwritten by an in-place replacement
        (reason ``replaced_by``), with the replacer's content key and a certificate that
        the replacer implies the replaced (uncertified if none can be produced).  Reads
        the old record from disk BEFORE it is overwritten.  Never raises; never changes
        the replacement decision."""
        try:
            import json as _json
            p = self.record_dir / old_id / f"{old_id}.json"
            if not p.exists():
                return
            old = _json.loads(p.read_text())
            der, used, cert = G.redundancy_certificate(old, [replacer_data])
            rk = G.record_content_key(replacer_data)
            G.archive_removal(self.record_dir, old, "replaced_by",
                              used_ids=(used or [replacer_data["id"]]) if der else None,
                              cert=cert if der else None, replacer_key=rk,
                              id_to_key={replacer_data["id"]: rk},
                              segment=segment, commit_index=commit_index)
        except Exception:
            pass

    def archive_forward_reject(self, prop, committed, segment=None, commit_index=None):
        """§D1: archive a main-process forward redundancy rejection
        (``redundant_vs_record_main``) to record/pruned.jsonl.  Never raises."""
        try:
            data = self.assemble_data(prop, "C0", [])
            existing = list(self.snapshot_records) + [c["data"] for c in committed]
            _, used, cert = G.redundancy_certificate(data, existing)
            id_to_key = {d["id"]: G.record_content_key(d) for d in existing if d.get("id")}
            G.archive_removal(self.record_dir, data, "redundant_vs_record",
                              used_ids=used, cert=cert, segment=segment,
                              commit_index=commit_index, id_to_key=id_to_key)
        except Exception:
            pass

    # ── v1.4 §I.4: renumber records to contiguous ids (segment end) ────────────
    def renumber_records(self):
        return G.renumber_records(self.record_dir)

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
