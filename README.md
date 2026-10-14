# Conjecture-Gym
Infinite Verifiable Conjectures for Training Mathematical Reasoning in Small LLMs

## PolyForge (v1.4.2)

PolyForge is the upstream data factory of Conjecture-Gym. Following the AlphaGeometry recipe, it samples random premises about a mathematical subject, runs a symbolic deduction engine forward, and turns the derived facts into new conjectures — each one **true, proved, and formally verified in Lean 4** before it enters the record.

No LLM is used anywhere in the pipeline: deduction is symbolic, truth is decided only by exact arithmetic, and Lean formalization is a deterministic translation of the deduction steps (no `sorry`).

### Framework and domains

PolyForge separates a **domain-agnostic engine** from the **domains** that plug into it:

- The engine (`anvil`, `generator`, `formalizer`, `scoring`) knows how to saturate a closed linear axiom base, enumerate and filter candidate conclusions, translate a proof to Lean and compile it, and score the result — without naming any subject-specific object.
- A **domain** supplies everything subject-specific through a single interface (`domains/base.py`): its variable set and Inventory (proved axiom base), its premise sampling and proposition format, its filters, its Lean statement/proof templates, its IRIS features, and its dataset.

This version ships two domains:

- **hex** — the original HexForge subject: p₆ of simple 3-connected planar maps (simple 3-polytopes). Fully wired and unchanged from v0.7; the 212-conjecture record is preserved and reproduced byte-for-byte.
- **graph** — graph theory on top of Mathlib's proved graph theorems. It has its own Lean project (Mathlib v4.34.0), a graph dataset (all 1253 graphs with ≤ 7 vertices), an Inventory (Mathlib theorems plus self-proved `GraphLemmas` — the Gallai identity α+τ=n, max degree ≤ edges, ℕ∞→ℕ finiteness/conversions, …), and generates conjectures that are linear (in)equalities among graph invariants under property premises. **Stage 2a (v1.2)** adds *product facts* whose proofs pass through a product of two invariants — the handshake degree bounds (n·min_deg ≤ 2m ≤ n·max_deg), the edge-count bounds (2m ≤ n²−n, and 4m ≤ n² for bipartite graphs) — while the conclusions stay linear.

### Products and McCormick envelopes (graph, v1.2)

Most classic graph facts are *linear in form but their proof passes through a product*: e.g. the handshake identity gives n·δ ≤ 2m, so δ ≥ 3 ⟹ 2m ≥ 3n. v1.2 carries each product as a proof-only **auxiliary variable** (`P_n_mindeg = n·min_deg`, `P_n_maxdeg = n·max_deg`, `N2 = n·n`) — like the hex domain's `W`/`J`, these never appear in a proposition. In each reasoning context the engine takes the already-proved lower/upper bounds `a ≤ x ≤ A`, `b ≤ y ≤ B` of the factors and emits the **McCormick envelope** of `P = x·y` (e.g. from `x ≥ a`, `y ≥ b` and `(x−a)(y−b) ≥ 0`: `P ≥ b·x + a·y − a·b`) as a new fact via the **product inference step** (`mul_nonneg` + `ring_nf` + `linarith` in Lean). Combined with a product fact (e.g. `P_n_mindeg ≤ 2m`) this yields a linear conclusion. **Linear derivability** is redefined so a conjecture is kept only when the full engine (products, envelopes, rounding, case split) beats what the *linear* facts alone prove: `depth_type` gains the value `product_needed` (the lift comes from a product), which — like `split_needed` — belongs to the main phase. A degenerate-premise filter discards premises that force `max_deg ≤ 1`, `m ≤ 1`, or `n ≤ 3`.

### Pipeline

```
premises → anvil (deduction) → generator (selection) → formalizer (Lean) → scoring → record
```

1. The domain samples premises that at least one dataset object satisfies.
2. **anvil** derives new facts from the domain's axiom base using four inference actions: linear combination, integer rounding, case split, and — for domains with product facts (graph, v1.2) — a product step (a McCormick envelope on an auxiliary product variable).
3. The domain keeps the conclusions it cares about, removes trivial and duplicate ones, and extracts minimal proofs by traceback.
4. Every candidate is checked exactly, regression-tested on the domain's dataset, and translated to Lean. Only conjectures whose Lean file compiles (no `sorry`) are written to the record.
5. **scoring** attaches an IRIS score and a hardness score.

### Structure

```
Conjecture-Gym/
├── run.py                      # entry point (python -m run polyforge <domain> …)
└── PolyForge/
    ├── anvil/deducer.py        # generic engine: facts, saturation, LP, traceback, recheck
    ├── generator/generator.py  # generic driver: cache, renumber, soundness, record IO, worker
    ├── formalizer/formalizer.py# generic Lean compilation (single / batch, bisection)
    ├── scoring/
    │   ├── iris.py             # IRIS core: T + R + L over domain feature vectors
    │   └── hardness.py         # proof difficulty / statement length
    ├── env/                    # core training environment (v1.3, domain-agnostic)
    │   ├── tasks.py            #   task format, task_id, skeleton, difficulty, split
    │   ├── verifier.py         #   resident-REPL verifier + layered anti-cheat checks
    │   ├── reward.py           #   RL reward_fn + proof extraction
    │   ├── evaluate.py         #   pass@1 / pass@k evaluation
    │   ├── export.py           #   tasks/train/test/sft/metadata/README export
    │   └── setup_repl.sh       #   build the pinned Lean REPL (git-ignored vendor/)
    └── domains/
        ├── base.py            # the Domain interface
        ├── hex/               # the p₆ domain (original HexForge content)
        │   ├── inventory.py   #   Python counterpart of Inventory.lean + HexLemmas.lean
        │   ├── deduction.py   #   base directions, split specs, B&B vars, vars_from_pvec
        │   ├── generator.py   #   premise sampling, candidate search, filters, formula, pipeline
        │   ├── formalizer.py  #   proof steps → Lean (SimplyCon3ConnectedMap), compile wrappers
        │   ├── iris.py        #   hex IRIS features
        │   ├── domain.py      #   HexDomain: wires the above to the engine
        │   ├── lean/          #   Inventory.lean (read-only), HexLemmas.lean  (Mathlib v4.30.0)
        │   ├── data/          #   plantri_pool.json (real simple 3-polytopes)
        │   └── record/        #   C{n}/C{n}.json, C{n}.md, C{n}.lean
        └── graph/             # the graph domain (skeleton)
            ├── domain.py      #   GraphDomain (not yet wired to an Inventory)
            ├── lean/          #   independent Lean project, GraphLemmas.lean  (Mathlib v4.34.0)
            └── data/          #   graph_pool.json (all graphs with ≤ 7 vertices)
```

### Usage

Run from the `Conjecture-Gym` root:

```bash
python -m run polyforge hex                 # run until Ctrl+C
python -m run polyforge hex 50              # 50 split_needed, then up to floor(50/4)=12 rounding_only
python -m run polyforge hex --minutes 30    # run for 30 minutes
python -m run polyforge hex 50 --minutes 30 # stop at whichever comes first
python -m run polyforge graph               # prints a notice (graph Inventory not yet wired up)
```

Generation runs in two phases: a main phase that produces `N` harder
`split_needed` conjectures, then a supplement phase that adds at most `floor(N/4)`
easier `rounding_only` conjectures (so the easy tier is at most 20% of the record). With
`--minutes M` the main phase gets 85% of the budget and the supplement phase the
remaining 15%.

Options: `--seed S` (base seed), `--workers W` (number of worker processes;
default auto-sized from cores and memory). Generation runs across worker
processes but results are consumed in strict premise-index order, so the record
is independent of the worker count. When both `N` and `--minutes M` are given the
run stops at whichever comes first (target `N` reached or budget `M` elapsed).

**Reproducible multi-segment production run (v1.4.1).** The graph record is built by a
sequence of segments with fixed seeds, each targeting 80 records with a 150-minute cap:

```bash
python -m run polyforge graph 80 --minutes 150 --seed 2024   # segment 1 (record cleared first)
python -m run polyforge graph 80 --minutes 150 --seed 2025   # segment 2 (accumulates), …
```

Seeds run `2024, 2025, 2026, …`. The first segment starts from an empty record; each later
segment accumulates on the previous one's record.

**Deterministic work budget (v1.4.2).** A segment's main phase stops after at most
`--max-groups G` premise groups (a *work* budget, not wall-clock), so a segment's content
is a deterministic function of (seed, target, `G`) — independent of machine speed and
worker count. The main phase returns an explicit end reason — `TARGET_REACHED`,
`BUDGET_EXHAUSTED` or `CANDIDATES_EXHAUSTED` — printed in `SEGMENT STATS`. `--minutes` is
now only a **safety cap**: exceeding it aborts the run loudly (exit 3) and is never a
stop-rule signal. **Stop rule (v1.4.2):** after a segment, stop iff (a) two *consecutive*
segments end `BUDGET_EXHAUSTED`, or (b) a segment ends `CANDIDATES_EXHAUSTED`, or (c) its
net gain (new writes − reverse-pruned) falls below 20% of the first segment's net.

**Run safety (v1.4.2).** The run takes an exclusive `flock` on the record directory for its
whole lifetime and stamps a per-run token on `record/.run_token`; a second run (or an
orphan that inherited a descriptor) cannot acquire the lock and is told the holder PID.
Every record write verifies the on-disk token still matches its own, so a stale/orphan
writer whose token was rotated away by a restore is refused. Only the main process writes
the record (workers merely return results), and each worker is killed automatically when
its parent dies (`PR_SET_PDEATHSIG` on Linux). Record writes are atomic (temp dir +
`os.replace`), so a crash leaves only complete records and a restart needs zero manual
steps.

**Production driver (v1.4.2, `scripts/run_production.py`).** The cross-segment driver lives
in the repo. Before each segment it backs up the whole record (C-dirs + `pruned.jsonl` +
`.production_state.jsonl`); after each completed segment it appends one line to
`record/.production_state.jsonl` with the stats, the `gen/forward/reverse/compile/other`
timing breakdown, and the sha256 of the record and of `pruned.jsonl`. On start it verifies
those hashes against disk — matching ⇒ resume from the next seed, mismatch ⇒ restore the
in-progress segment's pre-run backup and redo it (zero manual steps; a SIGKILL mid-commit
resumes to a byte-identical record). When the run ends (or stops early) the driver itself
runs the post-run audits — basis + `closure_audit`, reproducibility of segment 1, export +
stratified split + oracle + anti-cheat + standalone recompile, and the L0–L3 tactic
baselines — into `record/production_summary.json`, so the audits complete even if the
launching session dies. `PolyForge/env/baseline.py` adds the L2 (all Inventory facts incl.
products, then `nlinarith`) and L3 (`interval_cases` on ≤2 small-range variables) tactic
baselines; `PolyForge/env/oracle_check.py` runs the oracle + anti-cheat + recompile audit.

### Axiom base

Each domain reasons only over its own closed axiom base. The hex domain uses the three theorems in `Inventory.lean` (Juc_EulerFormula, JucovicTheorem, Barnette_P6Bound) and elementary sum lemmas proved without `sorry` in `HexLemmas.lean`; `Inventory.lean` is never modified. The graph domain's `GraphLemmas.lean` builds on Mathlib's proved graph theorems.

### Conjecture format (graph)

A graph conjecture is `if (<premises>), then (<conclusion>)`, where every premise and the conclusion concern a finite simple graph `G`.

**Variables** (all ℕ-valued): `n` (vertices), `m` (edges), `max_deg`, `min_deg`, `chi` (chromatic number), `omega` (clique number), `alpha` (independence number), `tau` (vertex-cover number), `diam` (diameter), `radius`, `girth`.

**Properties** (premises only): `is_connected`, `is_tree`, `is_acyclic`, `is_bipartite`, `not_bipartite`, `has_cycle`, `is_regular(d)`, `is_k_edge_connected(k)`, `nontrivial` (n ≥ 2). Implications are applied automatically (`is_tree ⟹ is_connected ∧ is_acyclic`, `is_acyclic ⟹ is_bipartite`, `has_cycle ⟺ ¬is_acyclic`, `is_bipartite ⟺ chi ≤ 2`).

**Nonempty.** All graphs are assumed to have at least one vertex (`n ≥ 1`); the Lean statements carry `[Nonempty V]` and the 0-vertex graph is excluded from the dataset. Elementary facts such as `chi ≥ 1`, `omega ≥ 1`, `alpha ≥ 1` therefore hold unconditionally.

**Finiteness restrictions.** `diam`/`radius` are in ℕ∞ and finite only for connected graphs, so they may appear (in premises, conclusion, or proof) only when `is_connected` is a premise; `girth` is in ℕ∞ and finite only when the graph has a cycle, so it needs `has_cycle`. `chi` and `tau` are ℕ∞ but always finite for a finite graph (used via `toNat`).

**Format rules.** Premises: 0–2 property premises and 1–2 numeric premises (an upper/lower bound on a variable, or a two-variable relation restricted to `x ≤ y`, `x ≥ y`, `x ≤ 2·y`, `x ≥ 2·y`). Conclusion: a linear (in)equality with a **primary variable** (coefficient 1 or 2) and at most 3 other terms (coefficients |·| ≤ 3); both upper and lower bounds are mined. A term is dropped from a conclusion only when the shortened version is both still provable AND still **implies** the original conclusion (a premise-free logical check: e.g. `m ≥ 6` does not replace `2m ≥ 3n`, since `m ≥ 6` does not imply `2m ≥ 3n`); every premise not needed to prove the conclusion — including premises implied by the others or true from the Inventory alone — is removed by re-proving with the full engine.

**Canonical form (v1.2.2).** Several Inventory *equalities* let the same conclusion be written many ways: the Gallai identity `α + τ = n` (always), `m = n − 1` under `is_tree`, and `2m = d·n`, `max_deg = min_deg = d` under `is_regular(d)`. To avoid recording disguised duplicates, every conclusion is reduced to a **canonical form** by substituting, in a fixed order, `τ → n − α`, then `m` and `max_deg`/`min_deg` where the identity is active, then clearing to coprime integers; de-duplication, skeletons, the decomposability / redundancy / significance / triviality filters all run on this canonical form, and `τ` is dropped from the primary rotation (every `τ`-primary conclusion canonicalises to an `α` one). The conclusion is **displayed** in the shortest equivalent form (fewest terms; ties → the canonical form), still with the primary variable alone on one side; the Lean proof derives the generation form and closes to the displayed form with one extra linear-combination step over the active identity wrappers. The JSON records both the displayed `conclusion` and the `canonical_form`. The primary variable rotates deterministically across premise sets (over the finiteness-valid invariants) for balance. The conclusion is displayed with the primary variable alone on one side with a positive coefficient (e.g. `chi >= 2*omega - 2*alpha - 2` rather than `-chi + 2*omega - 2*alpha <= 2`), and the Lean statement matches this form. Conclusions equivalent to a known property are tagged in the JSON for stage-3 retrieval: `properties` lists the property premises, and `conclusion_property` names the equivalent property when the conclusion is one of `chi ≤ 2 → is_bipartite`, `chi ≤ 1 → edgeless`, `chi ≥ 3 → not_bipartite`, `max_deg = min_deg → is_regular`, or (under `is_connected`) `m = n − 1 → is_tree`; otherwise it is `null`. These tags are metadata only (no Lean proof required).

**Examples.**

```
if ((is_connected) and (has_cycle) and (girth >= 5)), then (diam >= 2)
if ((is_tree) and (n >= 10)), then (m >= 9)
if ((not_bipartite)), then (chi >= 3)
```

### Generation quality (v1.3.1)

Two further filters cut low-value graph conjectures:

- **One representative per instance family.** A conjecture whose proof rests on a
  single *substantive* Inventory fact (everything except the base scaffolding —
  variable non-negativity, `n ≥ 1`, `chi/omega/alpha ≥ 1`, and the property-closure
  implications) is an *instance* of that fact; the JSON records it as `instance_of`
  (else `null`). Parametric instances that differ only in constants — e.g.
  `n ≥ 4 ⟹ 2·min_deg ≤ m`, `n ≥ 6 ⟹ 3·min_deg ≤ m`, … — are grouped into a
  *family* (the fact + the constant-free premise skeleton + the canonical
  conclusion's variable set and direction), and only the best representative per
  family is kept (the rest are dropped as `instance_family_duplicate`).
- **Coefficient-split decomposability.** The decomposability check now also splits a
  shared variable's coefficient `c_v = a + b` (both nonzero, |·| ≤ 3) across the two
  parts, so a conclusion like `omega − 2m + 2·min_deg ≤ 1` is recognised as the sum
  of `omega − m ≤ 1` and `2·min_deg − m ≤ 0` and dropped (`decomposable_split`). A
  linear-relaxation bound prunes hopeless splits before the full engine runs; a
  per-candidate time budget guards against pathological cases (`decomposition_timeout`).
- **Weakened forms promoted to their core (v1.3.2).** A conclusion `L ≥ c` is a
  *weakened* form when it is a valid inequality `A ≥ b_A` on (possibly) the same
  variables plus a single-variable bound `k·v ≥ b_B` with `b_A + b_B ≥ c` (`A = L − k·v`,
  `A` nonzero and not proportional to `L`). For example `min_deg ≥ 2 ⟹ 3m − n ≥ 6`
  is `m − n ≥ 0` padded with `2m ≥ 6`. Rather than discard it, PolyForge **promotes**
  the cleaner core `A ≥ b_A` back through the full pipeline (premise minimisation,
  proof reconstruction, every filter) and drops the padded original
  (`weakened_promoted`). A promoted core may itself be weakened at most once more
  (then `weakened_depth_limit`). The recorded JSON carries `promoted_from` (the
  original conclusion) and `instance_of`. The weakened check shares its split tree,
  bound cache and time budget with the coefficient-split check.
  **Cleanest core first (v1.4).** When several weakenings `A ≥ b_A` are valid,
  PolyForge now selects the **cleanest** core — fewest variables in `A`, then the
  smallest sum of `|coefficients|`, then the fixed variable/`k` enumeration order — so
  the padded conclusion reaches its true core in a *single* promotion step instead of
  peeling one layer at a time (e.g. `min_deg ≥ 2 ⟹ 3m − n ≥ 6` goes straight to
  `m ≥ n`, not via `3m − 2n ≥ 3`).
- **Degeneracy (v1.3.2).** A premise set is dropped (`degenerate_premises`) when the
  full engine proves any of `n ≤ 4`, `m ≤ 4`, `max_deg ≤ 1` (only a handful of small
  graphs remain — essentially a finite enumeration) or `chi ≥ n` (a complete graph,
  whose invariants are all fixed by `n`). The firing condition is recorded.

### Redundancy and reverse pruning — a non-redundant basis (v1.4 / v1.4.1)

The forward logical-redundancy check only compares a **new** conjecture against records
collected **earlier**, so a redundant conjecture recorded *before* the cleaner ones that
subsume it stays in the record forever. **Reverse pruning** closes the gap: after the main
process commits a new record `R`, every existing record `S` is re-examined and dropped
(`pruned_by_newer`) when `S` has become redundant now that `R` is present. The check runs
in the main process in strict commit order (so the record is worker-count-independent),
and only when `R` is usable under `S` (a cheap, cached premise-implication test filters out
most `S` first). The **same** redundancy test serves the forward check
(`redundant_vs_record`), reverse pruning, and the final basis-completeness audit.

**Redundancy means derivable from existing records (v1.4.1).** A proposition `S` is
redundant iff, using **linear combination and integer rounding only** — *no* products,
McCormick envelopes, product-variable facts (including the Turán conditional), case splits
or branch-and-bound — `S`'s conclusion is

1. **not** derivable from `S`'s premises and the (linear) Inventory **alone** — if it were,
   `S` is not redundant: generation already classifies it (linearly derivable ⇒ discarded;
   rounding ⇒ the supplement tier); **but**
2. **is** derivable once the conclusions of the existing records whose premises are implied
   by `S`'s premises are added (`S` itself never participates).

So redundancy requires that an existing record is genuinely *used*. **Premise implication**
(does `S`'s premises imply `R`'s?) is judged under the same restriction — property-closure
containment plus linear-combination/rounding entailment, **never** a product.

Why exclude products? Generation treats a product as *non-trivial* reasoning — a conjecture
is `product_needed` precisely because it needs one. v1.4 let the redundancy judgment use
products, so every one-product, no-split fact counted as "Inventory-derivable" and was
deleted as soon as any premise-compatible record appeared — deleting the most valuable
facts (`min_deg ≥ 3 ⟹ 2m ≥ 3n`, `is_bipartite ⟹ n ≤ 2α`, …). v1.4.1 restores consistency:
products are non-trivial everywhere, so such facts are kept unless a *record* (not just the
Inventory) makes them redundant.

Record-to-record premise implications are **cached** (keyed by the content of the premises)
and reused across commits, so reverse pruning stays cheap as the record grows; the cache is
a pure memo and never changes the result. Deletions during a run leave gaps in the `C{n}`
numbering; the record is **renumbered** to a contiguous `C1..Cn` (ascending id order) at the
end of each run — export `task_id`s are the hash of the name-neutralised Lean statement, so
they are unaffected. A final **basis-completeness audit** guarantees the two invariants: no
two records share a standard form, and no record is redundant in the sense above.

### Core training environment (v1.3)

Beyond generating conjectures, PolyForge ships its own **executable RL
environment** (`PolyForge/env/`) so the record can be used to train and evaluate
theorem-proving models directly. The tooling is domain-agnostic; v1.3 wires up
the **graph** domain only (the hex domain's Inventory uses `sorry`-as-axiom
placeholders, so its theorems cannot pass the standard-axioms check). Scoring
matches openai-math: a proof earns **reward 1** iff its statement is exactly the
reference statement, the Lean kernel accepts it, and it depends only on the
standard axioms (`propext`, `Quot.sound`, `Classical.choice`); otherwise 0.

- **Task format** (`env/tasks.py`). Each record becomes a task with a stable
  `task_id` (`graph-<12 hex>`, the hash of the name-neutralised, whitespace-
  normalised Lean statement — so the same statement always gets the same id), a
  fixed `lean_header` + `lean_statement` (ending in `:= by`), the `reference_proof`
  (the tactic block after `by`), the natural-language proof, a difficulty tier
  (hardness tertiles), a `skeleton` (property premises + constant-free premise
  shapes + canonical-conclusion variable set and direction), and a `train`/`test`
  split.
- **Verifier** (`env/verifier.py`). A submission is *only* the proof; the verifier
  prepends the fixed header and statement so the statement cannot be altered. It
  runs a resident Lean REPL (leanprover-community/repl, tag `v4.34.0`) that loads
  Mathlib + `GraphLemmas` once and reuses that environment for every submission,
  with multiple processes in parallel and automatic restart/crash-recovery.
  Layered anti-cheating, any failing layer ⇒ reward 0: a **static** scan (no
  top-level commands, `set_option`, `sorry`/`admit`, `#`-commands), a
  **compile** check under configurable `maxHeartbeats` and a wall-clock timeout,
  an **environment diff** (the proof may add only the target theorem and its
  auto-generated, name-prefixed helpers), an elaborated-**type** match against the
  cached reference statement, and an **axiom** check (standard axioms only).
- **Reward** (`env/reward.py`). `reward_fn(task_ids, completions)` for TRL/verl:
  it extracts the proof from the **last** ```` ```lean ```` block of each
  completion (dropping a leading `by`; no block ⇒ reward 0), then calls the
  batched verifier.
- **Evaluation** (`env/evaluate.py`). pass@1 and pass@k (unbiased estimator) over
  a `predictions.jsonl`, broken down by difficulty and split, with a status
  distribution.
- **Export** (`env/export.py`). `python -m PolyForge.env.export graph --out <dir>`
  writes `tasks.jsonl`, `train.jsonl`, `test.jsonl`, an SFT file `sft_train.jsonl`,
  `metadata.json`, and a `README.md`. The train/test split groups by skeleton (no
  skeleton straddles the split) and sends a whole group to test with a probability
  set by its hardest tier (hard 0.4, medium 0.2, easy 0.1), decided by the skeleton
  hash so the split is reproducible.

**Process count (v1.3.1).** A resident REPL reports ~6.5 GB RSS, but almost all of
that is the memory-mapped Mathlib `.olean` files, which the kernel shares across
processes — RSS counts the shared pages once per process, while `MemAvailable` is
charged only once. Measured on this project, each additional REPL process actually
costs ~0.8 GB. So the default process count is sized by `MemAvailable` minus a 20%
headroom divided by that measured marginal cost, capped at CPU cores − 2 (rather
than the far smaller RSS-based estimate). Measured throughput plateaus between 4 and
8 processes, so the default is additionally **capped at 8** (v1.3.2).

Build the REPL once with `PolyForge/env/setup_repl.sh` (it pins the repl commit and
the `v4.34.0` toolchain used by the graph Lean project). Example:

```bash
bash PolyForge/env/setup_repl.sh
python -m PolyForge.env.export graph --out /tmp/polyforge_graph_env
python -m PolyForge.env.verifier graph --task <task_id> --proof proof.lean
python -m PolyForge.env.evaluate graph predictions.jsonl --nprocs 2
```

Natural-language proofs now end at the displayed statement: when the generation
form differs from the displayed form, the markdown and JSON `proof.steps` carry
the final identity-rewrite step (re-rendered records are tagged
`"rendered_with": "1.3"`).

### Versioning

Each major version has eight minor versions, x.0 through x.7, after which the major version increments: 0.0 → … → 0.7 → 1.0 → … → 1.7 → 2.0 → … → 2.7. A third component (e.g. 0.6.1) marks a patch within a minor version.

### Changelog

- **v1.4.2** — `depth_type` now reflects the proof's actual structure (any case split ⇒ `split_needed`; else any product step ⇒ `product_needed`; else `rounding_only`) rather than the LP-necessity class used for phase acceptance; the main-phase counter is the hard tier (`split_needed` + `product_needed`), named accordingly. Deterministic work-budget stop rule (`--max-groups`; main phase returns `TARGET_REACHED` / `BUDGET_EXHAUSTED` / `CANDIDATES_EXHAUSTED`; `--minutes` is a safety cap only). Reverse pruning skips targets `N` cannot affect (premise-implication guard, cached) and prunes targets sequentially in id order so two mutually-derivable records are never both removed. Every forward rejection and reverse prune is archived to `record/pruned.jsonl` with a derivation certificate; a `closure_audit` checks every archived proposition is still derivable from the final record. Run safety: exclusive record-dir `flock` + per-run write token, workers killed with the parent (`PDEATHSIG`), atomic writes.

- **v1.4.1** — Redundancy (forward check, reverse pruning, basis audit) now means derivable from existing records by linear combination and rounding only, with premise implication under the same restriction, consistent with how product reasoning is valued at generation time; cached premise implication; production run re-done with a saturation-based stop rule.
- **v1.4** — Reverse pruning keeps the record a non-redundant basis regardless of discovery order; weakened forms promoted to their cleanest core in one step; reproducible multi-segment production run of the graph domain.
- **v1.3.2** — Weakened forms (a valid inequality on the same variables plus a single-variable bound) are replaced by their cleaner core, which is re-run through the full pipeline; degeneracy covers n ≤ 4, m ≤ 4, Δ ≤ 1 and complete graphs (χ ≥ n); verifier default capped at 8 processes.
- **v1.3.1** — Verifier sized by measured unique memory (shared .olean pages no longer double-counted), import configuration benchmarked; one representative per family of single-fact instances; decomposability with coefficient splitting of a shared variable.
- **v1.3** — Core training environment: stable task format, batched Lean verifier with layered anti-cheating checks (fixed statement, environment diff, elaborated type match, standard axioms only, heartbeat limits), RL reward function, pass@k evaluation, skeleton-based train/test split, SFT export; natural-language proofs now end at the displayed statement.
- **v1.2.2** — Canonical forms modulo active identities (Gallai, tree, regular) for deduplication and all filters, shortest equivalent form displayed; degeneracy check with full deductive power; relational premises restricted to naturally comparable pairs; diameter and cycle bounds added.
- **v1.2.1** — Fixed premise minimization and term dropping (a dropped term must still imply the original conclusion); always-true premises rejected at sampling; added n ≤ α·χ, Turán/Mantel bounds with a triangle-free case split, ω ≤ Δ + 1. (Diameter and cycle bounds were deferred here and added in v1.2.2.)
- **v1.2** — Graph domain stage 2a: products as auxiliary variables with McCormick envelopes and a new product inference step; handshake-based degree bounds, edge bounds, bipartite edge bound; linear derivability excludes products; degenerate-premise filter.
- **v1.1.2** — Graphs assumed nonempty; elementary textbook facts added systematically to prevent spurious proof depth; decomposability filter fixed; implied property premises removed; premises displayed in natural form.
- **v1.1.1** — Graph domain quality: elementary facts added to the inventory, simpler premises, rotating primary invariant, decomposability filter, redundancy check against existing records, Dalmatian significance (IRIS), primary invariant displayed on its own side.
- **v1.1** — Graph domain, stage 1: linear inventory from Mathlib plus self-proved lemmas (Gallai identity, max degree ≤ edges, …), property premises, conclusions on any invariant, property tags for future structural conjectures.
- **v1.0** — Renamed to PolyForge; domain-specific code moved into domains/; hex (p6) kept unchanged as the first domain; graph domain skeleton with its own Lean project (recent Mathlib) and a graph dataset.
- **v0.7** — Proved conjectures become lemmas: a lemma library selected from the record is used as conditional theorems; generation tracks how many layers of lemmas a proof builds on; hardness uses the expanded proof cost including lemmas; lemma proofs are inlined so every Lean file compiles on its own.
- **v0.6.7** — Cost-bounded re-proving finds the shortest proof for each conjecture; hardness computed from it (raw value, larger is harder); tiers removed; rounding-only conjectures capped at 20% instead of a fixed target.
- **v0.6.6** — Branch-and-bound case splits on fractional LP variables (shared nesting limit 3), predicted tiers, recalibrated work budget.
- **v0.6.5** — Out-of-order collection with in-order commit (removes head-of-line blocking); deterministic per-group work budget; difficulty tiers from actual proof structure; case-split nesting up to 3.
- **v0.6.4** — Parallel generation with deterministic ordering, batched Lean compilation, automatic HexLemmas rebuild, time-budgeted runs; rounding-only conjectures added in a final phase as the easy tier (20%).
- **v0.6.3** — Only conjectures whose proof requires a case split are kept; f_2 appears only in premises, never in conclusions; at most 3 terms besides p_6 in a conclusion.
- **v0.6.2** — Candidates from systematic direction enumeration with case-split LP bounds instead of random pairing; big_faces (sum over k ≥ 7) restored as a premise expression and display form.
- **v0.6.1** — Large faces listed individually (p_7 … p_10 plus a tail for k ≥ 11; upper limit configurable), arithmetic sharpness check via integer programming.
- **v0.6** — Skeleton de-duplication: conjectures differing only in constants share a skeleton; each skeleton keeps only its best conjecture (attained, then number of real polytopes attaining equality, then hardness), replaced in place.
- **v0.5** — Premise simplification (implied zero variables made explicit); compile check rejects any sorry; integer counter-model gate before Lean.
- **v0.4** — Lower bounds on p_6 only; p_6 must be essential (not padding via p_6 ≥ 0); premises with f_2 ≥ c for c > 28 skip pool-based checks and rely on Lean; deduction caching.
- **v0.3** — Both canonical-form and minimal-form p_6 checks; premises never mention p_6; redundant terms dropped from conclusions.
- **v0.2** — p_6 must appear in the minimal equivalent form; bounds strengthened to the strongest provable constant; conclusions must be attained by a real polytope; conclusions displayed as p_6 versus the rest.
- **v0.1** — Quality filters: premise de-duplication and minimization, canonical-form checks (f_2 eliminated), discard linearly derivable conclusions, step-by-step Lean translation, hardness counts only Inventory theorems.
- **v0.0** — First complete pipeline: anvil (inventory + deducer), generator, Lean formalizer with HexLemmas, IRIS and hardness scoring, `run.py` entry point.
