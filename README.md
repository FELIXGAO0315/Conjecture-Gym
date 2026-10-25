# Conjecture-Gym / PolyForge

> **A graph-theory conjecture factory that manufactures Lean-verified `(statement, proof)` pairs
> for training a downstream theorem prover — no language model in the generation loop.**

PolyForge mines inequalities and identities about graphs, proves each one by **symbolic forward
deduction**, and keeps it only if the generated `.lean` file compiles against the **Lean 4 kernel**
with no `sorry` and only the standard axioms. The output is a single training corpus —
`output/train_corpus.jsonl`, one row per theorem — built to give a downstream prover the three
things it needs at once: **volume, a difficulty gradient, and proof-paradigm diversity.**

```
   graph facts ──▶ forward deduction ──▶ candidate theorem ──▶ Lean 4 kernel ──▶ train_corpus.jsonl
    (invariants)      (LP, no LLM)        (filtered, scored)    (verify / reject)   (statement, proof)
```

Truth is decided by exact arithmetic and the Lean kernel, so the search that proposes conjectures is
*untrusted and disposable*: a bug there can waste compile time, but it can never put a false theorem
into the corpus. That is what makes the data safe to train on.

---

## Two stages: factory → prover

Conjecture-Gym is an upstream **factory** and a downstream **prover**, connected only by the corpus
file. Everything below up to *Design principles* documents the upstream; the prover has its own
section ([Downstream](#downstream--training--evaluating-the-prover)) at the end.

| Stage | Where | What it does | Framework |
|-------|-------|--------------|-----------|
| **Upstream — PolyForge** | `PolyForge/`, `run.py` | manufactures the Lean-verified `(statement, proof)` corpus — **no LLM in the loop** (symbolic deduction + Lean kernel) | [Architecture](#architecture) |
| **Downstream — nano-prover** | `training/` | fine-tunes a small LLM on that corpus (LoRA SFT) and scores it by **real Lean pass@k** | [Downstream](#downstream--training--evaluating-the-prover) |

The only thing the two stages share is `output/train_corpus.jsonl` — the factory grows it, the prover
trains on it.

---

## One command

```bash
python -m run graph
```

This is the whole pipeline. It drives **three graph-conjecture sources** into one deduplicated,
Lean-verified corpus:

| Source | What it contributes | How |
|--------|--------------------|-----|
| **curated** | **quality + difficulty** | the LP invariant engine under novelty curation (reverse-pruning to a non-redundant basis, a lemma library, multi-generation depth) → `graph/record/C*` |
| **harvest** | **volume** | the *same* LP engine with relaxed dedup, parallel generate + parallel Lean verify → `graph/record_train/T*` |
| **parametric** | **proof diversity** | `∀ n` theorems over **20 graph families** (`Cₙ`, `Kₙ`, `Pₙ`, star, Turán, circulant, complete-multipartite, Hasse, …) — a class the fixed-graph engine cannot express — each proved with a paradigm chosen per `(family, invariant)`, spanning **30 distinct proof strategies** → `graph/record_parametric/F*` |

```bash
python -m run graph 3000              # 3000 = harvest seeds (the volume knob)
python -m run graph --no-curated      # skip the curated engine, reuse the existing C*
python -m run graph --seeds 2000 --workers 12 --curated-groups 600
```

**The corpus accumulates.** `output/train_corpus.jsonl` is *grown*, never clobbered: each run merges
its new theorems into the existing corpus, **deduplicated by formula**, so repeated runs pile up more
`(statement, proof)` pairs over time. Because the harvest is deterministic in its seeds, the pipeline
keeps a **seed cursor** (`output/.corpus_state.json`) and advances it each run, so a later run explores
*new* premise sets instead of re-deriving the same theorems. The previous corpus is backed up
(`output/backups/`) before each write. When a run reports `+0 new`, the carrier is saturated at those
seeds — see below.

**Scheduling** (tuned for a typical 16-core / 15 GB box): `curated` and `harvest` each saturate all
cores and are Lean-memory-heavy, so they run in **sequence** (running them together would
oversubscribe cores for no throughput gain and risk OOM). The `parametric` phase uses a single Lean
REPL (≈1 core), so it runs **concurrently** with the heavy phases — reclaiming the cores that would
otherwise sit idle during it.

The raw curated engine is still available on its own (the build calls it internally):

```bash
python -m run polyforge graph 80           # 80 curated conjectures, then an easy tier
python -m run polyforge graph --minutes 30 # or a fixed budget
```

---

## What a row looks like

Each line of `train_corpus.jsonl` is one Lean-verified theorem, split into the **problem** the prover
is shown and the **target** it must produce:

```json
{
  "id": "C17", "domain": "graph", "source": "curated",
  "statement_lean": "theorem C17 (G : SimpleGraph V) [Fintype V] ... (h : G.minDegree ≥ 3) :\n    2 * G.edgeFinset.card ≥ 3 * Fintype.card V",
  "proof_lean": "by ...",
  "lean_full": "<compilable file>",
  "tactics": ["linarith", "omega"], "difficulty": 0.42, "verified": true
}
```

- `statement_lean` — the theorem signature up to `:=` (the prompt).
- `proof_lean` — everything after `:=` (the target).
- `lean_full` — the standalone file that actually compiled.
- `difficulty` — a *hardness* score (proof cost / statement length); the corpus spans easy→hard.
- `tactics` / `source` — the proof paradigm, for diversity analysis.

---

## The trust boundary

**Nothing enters the corpus unless the Lean 4 kernel accepts it.** A proposal becomes a record only
if its `.lean` file compiles with no `sorry` and depends only on the standard axioms
`propext`, `Quot.sound`, `Classical.choice` (the usual Mathlib trio). Verification is independent of
generation, so the correctness of the corpus rests on Lean + Mathlib, never on the search heuristics.

---

## Is this "infinite"? No — and that is by design

A fixed graph exposes only ~11 integer invariants (`n, m, χ, ω, α, Σdeg², …`). The space of
linear-inequality theorems among them is large but **finite**, and we measured it *saturating* — past
a point, raising the search budget buys almost nothing and difficulty stops climbing. That is an
honest negative result, and it shapes the whole design:

- **Volume** does not come from a bottomless carrier; it comes from the **harvest** mode keeping every
  valid, novel-enough, Lean-provable theorem rather than curating down to a minimal basis.
- **Difficulty** comes from proof *structure* — case splits (`by_cases`), integer rounding (`omega`),
  McCormick product envelopes (`mul_nonneg`/`ring`) — scored and spread across the corpus.
- **Diversity** comes from the **parametric** families (20 of them), whose `∀ n` proofs use 30 distinct
  paradigms the LP engine structurally cannot produce — parity `rcases`, `rw`/`simp`, handshake+`omega`,
  regularity, monotonicity, `calc`, negation, complement, `compl_compl`, antitone, graph-order `≤`,
  `le_antisymm`, `decide`, coloring construction, handshake-parity (`Even #odd-degree`), dart counting,
  term-mode citation — over invariants the fixed engine never sees (girth/egirth, diameter,
  eccentricity, chromatic/clique number, connectivity, matchings).

So PolyForge is a *bounded but deep* graph corpus, engineered for the three training properties — not
a claim of inexhaustibility.  **Growing it further means adding proof paradigms and families here (each
a hand-authored, Lean-verified strategy), not inflating family instances** — the downstream prover
learns from distinct strategies, not from the 100th specialization of one theorem.

---

## Architecture

PolyForge separates a reusable, **subject-agnostic engine** from the **graph domain** that plugs into
it. The engine never names a graph-specific object; a new subject would be a new module implementing
`domains/base.py`, not an engine rewrite.

```
run.py                      # entry: `python -m run graph`  (build)  ·  `python -m run polyforge graph`  (raw engine)
output/train_corpus.jsonl   # the deliverable
PolyForge/
├── engine/                 # domain-agnostic BACKEND
│   ├── deducer.py          #   LP saturation, integer rounding, case splits, McCormick products
│   ├── generator.py        #   generic driver: cache, record IO, parallel workers, in-order commit
│   ├── formalizer.py       #   generic Lean compilation (single / batch, bisection)
│   ├── scoring/            #   hardness (proof cost) · interestingness (GRAFFITI-style value)
│   └── soundness/          #   fail-closed verification kernel (canon, policies, props, lean_batch)
├── domains/
│   ├── base.py             #   the Domain interface
│   └── graph/
│       ├── domain.py       #     wires the engine to graph
│       ├── build.py        #     THE pipeline: curated + harvest + parametric → train_corpus.jsonl
│       ├── generator.py    #     fixed-graph LP engine (curated + harvest modes)
│       ├── parametric.py   #     ∀n family generator (proof-paradigm diversity)
│       ├── deduction.py · formalizer.py · inventory.py
│       ├── data/           #     the graph pool (invariants per sample graph)
│       └── record/ · record_train/ · record_parametric/   # curated · harvest · parametric (git-ignored)
├── env/                    # Lean verification toolkit: verifier, tasks, closure_complete,
│   │                       #   discardlog, replace_gate, analysis/ (audits), setup_repl.sh
├── lean/                   # shared Lean 4 + Mathlib v4.34.0 workspace (GraphLemmas; .lake git-ignored)
└── tests/                  # pytest correctness guard rail
```

### The forward pipeline (how one theorem is made)

```
premises → deducer → generator (select/filter) → formalizer (Lean) → scoring → record
```

1. Sample property premises that at least one real graph satisfies (e.g. `minDeg ≥ 3`, `is_tree`).
2. **deducer** derives new facts from the proved invariant base (`GraphLemmas`: Gallai `α + τ = n`,
   handshake bounds, Cauchy–Schwarz on degrees, Turán/Mantel conditionals, …) via linear combination,
   integer rounding, case split, and product envelopes.
3. The domain drops trivial / duplicate / decomposable / redundant conclusions and extracts a minimal
   proof by traceback. (Harvest mode relaxes the novelty filters to keep volume.)
4. Each candidate is translated to Lean and **compiled** — only files that pass (no `sorry`, standard
   axioms) survive.
5. **scoring** attaches a *hardness* score and an *interestingness* score (orthogonal signals).

---

## Quickstart

```bash
# 1. Build the shared Lean + Mathlib workspace and the resident REPL (once)
bash PolyForge/env/setup_repl.sh

# 2. Build the full training corpus (curated + harvest + parametric)
python -m run graph

# 3. The corpus is at output/train_corpus.jsonl  (statement_lean / proof_lean / lean_full per row)
```

The pipeline is reproducible (deterministic premise order, seeded work budgets) and crash-safe
(atomic writes, an exclusive record lock, a per-run write token, workers killed with the parent).

---

## Design principles

- **Verify, don't trust.** The Lean kernel is the only authority; the generator is disposable.
- **No LLM in the manufacturing loop.** Deduction is symbolic and truth is exact, so the data cannot
  be contaminated by the models it will train.
- **Quality is a filter, not an afterthought.** Redundancy pruning keeps the curated set a
  non-redundant basis; decomposability / degeneracy / weakened-form filters remove padding; hardness
  and interestingness are scored and separated.
- **Be honest about the carrier.** The graph invariant space is finite and saturates; volume comes
  from relaxed harvest and diversity from parametric families, not from pretending the space is
  bottomless.

---

## Downstream — training & evaluating the prover

The `training/` stage fine-tunes a small LLM to prove the corpus theorems (input = Lean statement,
output = Lean proof), then scores it the only honest way: by compiling the generated proofs through
the **same Lean kernel** the corpus was verified with.

```
prepare_data.py  →  sft_train.py  →  gen_preds.py  →  assessment.py
   split corpus      LoRA SFT        sample proofs      Lean-verified pass@k + report
```

### Framework

```
training/
├── train_kaggle.ipynb         # one-click: clone + install + train 0.5B + gen preds (free T4)
├── scripts/                   # the pipeline (train + generate run on the GPU box)
│   ├── prepare_data.py        # output/train_corpus.jsonl → scripts/data/{train,test}.jsonl
│   ├── sft_train.py           # LoRA SFT of a small instruct model → scripts/out/ (adapter)
│   ├── gen_preds.py           # sample k proofs per held-out statement → scripts/preds.jsonl
│   └── preds.jsonl            # the generated proofs (small, pushed back from Kaggle)
├── assessment/
│   └── assessment.py          # Lean-verify preds + write a report   (run LOCALLY)
└── output/                    # generated assessment reports (git-ignored)
```

The ML stack for this stage is `requirements_training.txt` at the repo root; the upstream factory
needs none of it (only Lean + the stdlib — its test-only deps are `requirements_graph.txt`).

### Workflow (local dev → Kaggle training → local eval)

1. **Local:** commit + push the repo (the corpus `output/train_corpus.jsonl` is included). The Lean
   verifier stays here for evaluation.
2. **On Kaggle** (GPU T4 x2, Internet On) — run `training/train_kaggle.ipynb`, or manually:
   ```bash
   git pull
   pip install -r requirements_training.txt
   python training/scripts/prepare_data.py
   python training/scripts/sft_train.py
   python training/scripts/gen_preds.py --n 100 --k 1
   ```
   then push the small `training/scripts/preds.jsonl` back.
3. **Local:** pull, then run the assessment:
   ```bash
   git pull
   python training/assessment/assessment.py           # Lean pass@k + report → training/output/
   ```

### Model choice

- Default: **Qwen/Qwen2.5-Coder-1.5B-Instruct** (T4 / 12 GB-class GPU friendly, knows Lean).
- CPU-only / fast iteration: **Qwen/Qwen2.5-Coder-0.5B-Instruct** (what the Kaggle notebook uses).
- Bigger GPU (24 GB+): try 3B, or the domain-specialized **DeepSeek-Prover-V2-7B** as the base.

### Notes

- Loss is computed on the proof only (`assistant_only_loss`), not the prompt.
- `assessment.py` is the *only* honest metric here: a proof counts iff the Lean 4 kernel accepts it
  (no `sorry`, standard axioms) — not string match. It also reports *why* proofs fail and whether the
  corpus is still teaching the model (lemma overlap, first-tactic match, truncation rate).
- The corpus is small; LoRA SFT teaches the proof *style/format*. Scale the corpus (more
  `python -m run graph` runs / more parametric families) before expecting hard wins.

---

## History (abridged)

- **v2.1–2.2** — the corpus accumulates across runs (dedup-append, advancing seed cursor); parametric
  grown from 8→**20 families** / 15→**30 proof paradigms** (circulant, complete-multipartite, Hasse,
  egirth, diameter, eccentricity, complement, `compl_compl`, antitone, graph-order `≤`, `decide`,
  coloring, handshake-parity, dart counting), with instance padding cut — strategy diversity over volume.
- **v2.0** — single graph pipeline: `python -m run graph` unifies curated + harvest + parametric into
  one `train_corpus.jsonl`; `parametric` runs concurrently; the project is graph-only (the legacy hex
  domain and the RL-reward/export track were removed).
- **v1.5–1.6** — interestingness scorer; the parametric (`∀ n`) family generator; graph deliverable
  and export; hardened fail-closed verification kernel and derivation certificates.
- **v1.1–1.4** — the graph domain: linear Inventory from Mathlib + self-proved `GraphLemmas`, property
  premises, McCormick product envelopes, reverse pruning to a non-redundant basis, reproducible
  deterministic runs.
- **v1.0** — the domain-agnostic engine + the `domains/` split.

---

**In one line:** PolyForge turns graph facts into Lean-proven `(statement, proof)` pairs with no model
in the loop — a bounded but deep corpus engineered for volume, difficulty, and proof diversity.
