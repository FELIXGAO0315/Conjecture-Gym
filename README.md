# Conjecture-Gym / PolyForge

> **A graph-theory conjecture factory that manufactures Lean-verified `(statement, proof)` pairs,
> and a nano-LLM prover trained on them — no language model in the generation loop.**

Conjecture-Gym has two stages connected by a single file, the corpus:

```
   ┌────────────────────────────────────────────────────────┐
   │  UPSTREAM — PolyForge            (no LLM in the loop)  │
   │  graph facts  →  forward deduction  →  Lean 4 kernel   │
   └───────────────────────────┬────────────────────────────┘
                               │
                               ▼   output/train_corpus.jsonl
                               │   one Lean-verified (statement, proof) / line
                               ▼
   ┌────────────────────────────────────────────────────────┐
   │  DOWNSTREAM — nano-prover                              │
   │  LoRA-SFT a small LLM  →  score it by REAL Lean pass@k │
   └────────────────────────────────────────────────────────┘
```

- **Upstream** (`PolyForge/`, `run.py`) manufactures the corpus by *symbolic* deduction, keeping a
  theorem only if its `.lean` compiles against the **Lean 4 kernel** (no `sorry`, standard axioms).
  Truth is decided by exact arithmetic, so the search is untrusted and disposable — a bug there wastes
  compile time but can never put a false theorem into the corpus.
- **Downstream** (`training/`) fine-tunes a small code LLM to produce proofs for those statements, and
  scores it by compiling its output through the *same* kernel.

| Stage | Where | What it does |
|-------|-------|--------------|
| **Upstream — PolyForge** | `PolyForge/`, `run.py` | manufactures the Lean-verified `(statement, proof)` corpus — no LLM in the loop |
| **Downstream — nano-prover** | `training/` | fine-tunes a small LLM on the corpus (LoRA SFT), scores it by real Lean pass@k |

The only thing the two stages share is `output/train_corpus.jsonl` — the factory grows it, the prover
trains on it. Each stage below is self-contained, with its own architecture **and its own changelog**.

<br>

---
---

# Upstream — the conjecture factory (PolyForge)

PolyForge mines inequalities and identities about graphs, proves each by symbolic forward deduction,
and keeps it only if the generated `.lean` compiles with no `sorry` and only the standard axioms. The
output is one training corpus — `output/train_corpus.jsonl`, one row per theorem — engineered to give
a prover three things at once: **volume, a difficulty gradient, and proof-paradigm diversity.**

```
   graph facts ──▶ forward deduction ──▶ candidate theorem ──▶ Lean 4 kernel ──▶ train_corpus.jsonl
    (invariants)      (LP, no LLM)        (filtered, scored)    (verify / reject)   (statement, proof)
```

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
seeds — see *Is this infinite?* below.

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

## The trust boundary

**Nothing enters the corpus unless the Lean 4 kernel accepts it.** A proposal becomes a record only
if its `.lean` file compiles with no `sorry` and depends only on the standard axioms
`propext`, `Quot.sound`, `Classical.choice` (the usual Mathlib trio). Verification is independent of
generation, so the correctness of the corpus rests on Lean + Mathlib, never on the search heuristics.

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
Its Python deps are `requirements_graph.txt` (numpy/scipy for the LP engine, networkx) plus Lean for
verification; it needs none of the downstream ML stack.

## Design principles

- **Verify, don't trust.** The Lean kernel is the only authority; the generator is disposable.
- **No LLM in the manufacturing loop.** Deduction is symbolic and truth is exact, so the data cannot
  be contaminated by the models it will train.
- **Quality is a filter, not an afterthought.** Redundancy pruning keeps the curated set a
  non-redundant basis; decomposability / degeneracy / weakened-form filters remove padding; hardness
  and interestingness are scored and separated.
- **Be honest about the carrier.** For a *fixed* invariant set the graph space is finite and saturates;
  volume comes from relaxed harvest and diversity from parametric families, not from pretending the
  space is bottomless. The lever that genuinely re-opens it is **adding invariants** (v2.3: ν/γ/κ) —
  each one, with its Lean-verified bounds, enlarges the reachable conjecture space and the difficulty
  ceiling.

## Upstream changelog

- **v2.3** — **new graph invariants: matching number ν, domination number γ, vertex-connectivity κ** —
  each self-defined in `GraphLemmas.lean` with Lean-verified ℤ bound lemmas (2ν≤n, ν≤τ, γ≤α, κ≤δ, …;
  zero `sorry`, standard axioms) and wired end-to-end, de-saturating the carrier (one round adds
  hundreds of fresh ν/γ/κ theorems, difficulty up to ~15, including conjectures coupling two new
  invariants). Reverse-prune made **~100–500× faster** (goal-only directions for the record-fact
  derivability check + an O(1) `depth_type` fast-path for the inventory-alone check), verified to
  leave the pruned set byte-for-byte identical.
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

<br>

---
---

# Downstream — the nano-prover (v0.2)

The `training/` stage fine-tunes a small LLM to prove the corpus theorems (input = Lean statement,
output = Lean proof), then scores it the only honest way: by compiling the generated proofs through
the **same Lean kernel** the corpus was verified with.

> **Versioning.** The downstream nano-prover is versioned independently of the upstream PolyForge
> factory above. It is at **v0.2** (2 training rounds so far — see `training/output/`); the upstream
> changelog (…, v2.3) tracks the corpus generator, not this model. Each nano-prover run just consumes
> whatever `output/train_corpus.jsonl` currently holds (now 6413 theorems, incl. the v2.3 ν/γ/κ set).
> It trains on the **full corpus** (a small held-out split is kept only for the Lean-verified pass@k).

```
prepare_data.py  →  sft_train.py  →  gen_preds.py  →  assessment.py
   split corpus      LoRA SFT        sample proofs      Lean-verified pass@k + report
```

Training + generation run on the local GPU; the Lean-verified scoring runs on the same box (where the
Mathlib workspace is). One `bash training/scripts/run.sh all` does train + generate; `python -m assess`
scores the generated `preds.jsonl`.

## Framework

```
training/
├── scripts/                   # the pipeline (train + generate run on the GPU box)
│   ├── run.sh                 # one entry: `run.sh train|gen|all` (install + prepare + train + generate)
│   ├── prepare_data.py        # output/train_corpus.jsonl → scripts/data/{train,test}.jsonl
│   ├── sft_train.py           # LoRA SFT of a small instruct model → model/ (adapter, at repo root)
│   ├── gen_preds.py           # sample k proofs per held-out statement → scripts/preds.jsonl
│   └── preds.jsonl            # the generated proofs (small text file)
├── model/                     # the TRAINED ADAPTER (your deliverable: base + this LoRA = the prover)
├── assessment/
│   └── assessment.py          # Lean-verify preds + write a report
└── output/                    # generated assessment reports: <ordinal>_training_report-<date>.md (git-ignored)
```

The ML stack is `requirements_training.txt` at the repo root (the upstream factory needs none of it —
its own deps are `requirements_graph.txt` + Lean).

## Setup (one-time, on the GPU box)

Use `python -m pip` (in a bare conda env the `pip` shim is often absent; `python -m pip` always
works — if even that is missing, `python -m ensurepip --upgrade` or `conda install pip` first).

```bash
# 1. Python deps.  Engine (numpy/scipy/networkx) — needed by BOTH the corpus factory and the
#    assessment — plus a CUDA build of torch (match your CUDA) and the SFT stack:
python -m pip install -r requirements_graph.txt
python -m pip install torch --index-url https://download.pytorch.org/whl/cu121
python -m pip install -r requirements_training.txt

# 2. Lean workspace — needed for `python -m assess` (it compiles the generated proofs).
#    (a) Lean toolchain (provides `lake`), if not already installed:
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh -s -- -y && source "$HOME/.elan/env"
#    (b) the pinned REPL + the GraphLemmas library — `cache get` pulls PREBUILT Mathlib
#        oleans so this is minutes, not the hours a full Mathlib compile would take:
bash PolyForge/env/setup_repl.sh
( cd PolyForge/lean && lake exe cache get && lake build GraphLemmas )
```

`run.sh train` also `python -m pip`-installs the transformers stack inline. Training/generation need
step 1 (torch); only the assessment needs the step 2 Lean build.

## Workflow (local GPU — edit config, run, assess)

The whole loop runs on one GPU box. The run config lives in `training/scripts/run.sh`; edit it to
change a run.

1. **Edit the CONFIG block** in **`training/scripts/run.sh`** (`SFT_MODEL`, `SFT_EPOCHS`, `GEN_K`,
   `GEN_MAXTOK`, …).
2. **Train + generate:**
   ```bash
   bash training/scripts/run.sh all     # install deps, prepare data, LoRA fine-tune, then generate proofs
   # or run the phases separately:  run.sh train   |   run.sh gen
   ```
3. **Assess (Lean-verified):**
   ```bash
   python -m assess       # Lean pass@k + report → training/output/
   ```

## The assessment report

`assessment.py` re-verifies every generated proof through the Mathlib + GraphLemmas REPL and writes
`training/output/<ordinal>_training_report-<date>.md` (`1st_…`, `2nd_…`, auto-incrementing per run)
containing:

- **pass@k** (Lean-kernel verified) and *which* theorems were solved;
- **why the rest failed**, bucketed by Lean error (parse/truncation, unknown lemma, unsolved goals,
  tactic-failed, type mismatch, …);
- **did the model learn?** — truncation rate, first-tactic match, and lemma-name overlap with the
  reference proofs;
- a **verdict** on whether the upstream corpus is still useful for this nano-LLM.

This is the *only* honest metric here: a proof counts iff the Lean 4 kernel accepts it (no `sorry`,
standard axioms) — never string match against the reference.

## Model choice

- Default (`run.sh`): **Qwen/Qwen2.5-Coder-3B-Instruct** (knows Lean; fine on a 24 GB-class GPU).
- Fast iteration: **Qwen/Qwen2.5-Coder-1.5B-Instruct** or **0.5B-Instruct**.
- Bigger GPU: try 7B/14B, or the domain-specialized **DeepSeek-Prover-V2-7B** as the base.

All knobs are env-overridable, e.g. `SFT_MODEL=…`, `SFT_EPOCHS=3`, `SFT_MAX_SEQ=…`.

## Training report

One row per run. Full per-run detail (failure buckets, learning signals, verdict) is in the generated
`training/output/<ordinal>_training_report-<date>.md` from `assessment.py`.

| # | date | base · config | pass@k | lemma overlap | top failure | takeaway |
|---|------|---------------|-------:|--------------:|-------------|----------|
| 1 | 2026-10-25 | 0.5B · 1 ep · gen 512 · k1 | **2/100** | 0.58 | 59% truncated | corpus is teaching; decoding-limited → raise gen length, 1.5B, 3 ep |
| 2 | 2026-10-25 | 1.5B · 3 ep · gen 1024 · k3 | **54/100** | 0.81 | tactic not closed (23%) | big jump from 2%; truncation 59%→17%, first-tactic 38%→82% — levers worked; next: `--k 5`, grow corpus |

<br>

---

**In one line:** Conjecture-Gym turns graph facts into Lean-proven `(statement, proof)` pairs with no
model in the loop (upstream), then trains and honestly Lean-scores a small prover on them (downstream).

<br>

---
---

# Model — the trained nano-prover

> **The deliverable.** A small LLM fine-tuned to prove graph-theory theorems in Lean 4. Download it,
> give it a statement, get back a Lean proof the kernel accepts.

## What it is

- **Base:** `Qwen/Qwen2.5-Coder-1.5B-Instruct` (public; auto-downloaded) **+** a **LoRA adapter** at
  [`model/`](model/) — the adapter *is* the trained part (a few tens of MB of weights).
- **Input:** a Lean 4 theorem **statement** (a graph-invariant inequality/identity, in the corpus's
  format — the signature up to `:=`).
- **Output:** a candidate Lean 4 **proof** (a `by …` tactic block).
- **Quality:** Lean-kernel-verified **pass@3 = 54%** on held-out statements (run 2 — see the Training
  report above). A proof "counts" only if Lean 4 compiles it with no `sorry` and standard axioms.

## How to use it

```bash
git clone https://github.com/FELIXGAO0315/Conjecture-Gym.git && cd Conjecture-Gym
pip install transformers peft torch
```

```python
from transformers import AutoModelForCausalLM, AutoTokenizer
from peft import PeftModel

base = "Qwen/Qwen2.5-Coder-1.5B-Instruct"                 # auto-downloaded from Hugging Face
tok   = AutoTokenizer.from_pretrained(base)
model = PeftModel.from_pretrained(AutoModelForCausalLM.from_pretrained(base), "model")

statement = "theorem ex (G : SimpleGraph V) [Fintype V] ... : 2 * G.edgeFinset.card ≥ 3 * Fintype.card V"
msgs = [{"role": "user", "content": f"Prove this Lean 4 theorem:\n\n```lean\n{statement} :=\n```"}]
ids  = tok.apply_chat_template(msgs, add_generation_prompt=True, return_tensors="pt")
print(tok.decode(model.generate(ids, max_new_tokens=1024)[0][ids.shape[1]:], skip_special_tokens=True))
```

To **check** a generated proof, compile `statement := proof` against the Lean workspace in
`PolyForge/lean` (that is exactly what `training/assessment/assessment.py` does). A GPU makes
generation fast; CPU works but is slow.

## The goal — and where this model honestly stands

The north star: **feed in a conjecture — including an existing unsolved one — and get back both a
machine-checked Lean proof and a readable written proof (Markdown / PDF).** That is what would make
this a genuinely useful prover.

| capability | status |
|---|---|
| prove graph-theory statements *in the corpus's Lean format* | ✅ **working** — 54% Lean-verified (pass@3) |
| output a Lean proof the kernel accepts | ✅ working |
| render the Lean proof into a written Markdown / PDF proof | ⏳ **not yet** — planned (next: a `prove.py` that generates → verifies → renders) |
| take a conjecture in **plain natural language** (not pre-formalized Lean) | ⏳ not yet — needs an autoformalization front-end |
| attack **open / unsolved** conjectures | ✖ **out of scope for a 1.5B model** — that is research-frontier; this model proves *in-distribution* graph theorems, not open problems |

So today it is an honest, Lean-verified **graph-theory proof assistant for formalized statements**, not
an open-problem solver — and every claim it makes is checked by the Lean kernel, never asserted.
Growing the corpus (upstream) and scaling the model lift the 54%; the written-proof rendering and the
natural-language front-end are the next milestones toward the north star.
