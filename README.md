# Conjecture-Gym
Infinite Verifiable Conjectures for Training Mathematical Reasoning in Small LLMs

## PolyForge (v1.2)

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
is independent of the worker count.

### Axiom base

Each domain reasons only over its own closed axiom base. The hex domain uses the three theorems in `Inventory.lean` (Juc_EulerFormula, JucovicTheorem, Barnette_P6Bound) and elementary sum lemmas proved without `sorry` in `HexLemmas.lean`; `Inventory.lean` is never modified. The graph domain's `GraphLemmas.lean` builds on Mathlib's proved graph theorems.

### Conjecture format (graph)

A graph conjecture is `if (<premises>), then (<conclusion>)`, where every premise and the conclusion concern a finite simple graph `G`.

**Variables** (all ℕ-valued): `n` (vertices), `m` (edges), `max_deg`, `min_deg`, `chi` (chromatic number), `omega` (clique number), `alpha` (independence number), `tau` (vertex-cover number), `diam` (diameter), `radius`, `girth`.

**Properties** (premises only): `is_connected`, `is_tree`, `is_acyclic`, `is_bipartite`, `not_bipartite`, `has_cycle`, `is_regular(d)`, `is_k_edge_connected(k)`, `nontrivial` (n ≥ 2). Implications are applied automatically (`is_tree ⟹ is_connected ∧ is_acyclic`, `is_acyclic ⟹ is_bipartite`, `has_cycle ⟺ ¬is_acyclic`, `is_bipartite ⟺ chi ≤ 2`).

**Nonempty.** All graphs are assumed to have at least one vertex (`n ≥ 1`); the Lean statements carry `[Nonempty V]` and the 0-vertex graph is excluded from the dataset. Elementary facts such as `chi ≥ 1`, `omega ≥ 1`, `alpha ≥ 1` therefore hold unconditionally.

**Finiteness restrictions.** `diam`/`radius` are in ℕ∞ and finite only for connected graphs, so they may appear (in premises, conclusion, or proof) only when `is_connected` is a premise; `girth` is in ℕ∞ and finite only when the graph has a cycle, so it needs `has_cycle`. `chi` and `tau` are ℕ∞ but always finite for a finite graph (used via `toNat`).

**Format rules.** Premises: 0–2 property premises and 1–2 numeric premises (an upper/lower bound on a variable, or a two-variable relation restricted to `x ≤ y`, `x ≥ y`, `x ≤ 2·y`, `x ≥ 2·y`). Conclusion: a linear (in)equality with a **primary variable** (coefficient 1 or 2) and at most 3 other terms (coefficients |·| ≤ 2); both upper and lower bounds are mined. The primary variable rotates deterministically across premise sets (over the finiteness-valid invariants) for balance. The conclusion is displayed with the primary variable alone on one side with a positive coefficient (e.g. `chi >= 2*omega - 2*alpha - 2` rather than `-chi + 2*omega - 2*alpha <= 2`), and the Lean statement matches this form. Conclusions equivalent to a known property are tagged in the JSON for stage-3 retrieval: `properties` lists the property premises, and `conclusion_property` names the equivalent property when the conclusion is one of `chi ≤ 2 → is_bipartite`, `chi ≤ 1 → edgeless`, `chi ≥ 3 → not_bipartite`, `max_deg = min_deg → is_regular`, or (under `is_connected`) `m = n − 1 → is_tree`; otherwise it is `null`. These tags are metadata only (no Lean proof required).

**Examples.**

```
if ((is_connected) and (has_cycle) and (girth >= 5)), then (diam >= 2)
if ((is_tree) and (n >= 10)), then (m >= 9)
if ((not_bipartite)), then (chi >= 3)
```

### Versioning

Each major version has eight minor versions, x.0 through x.7, after which the major version increments: 0.0 → … → 0.7 → 1.0 → … → 1.7 → 2.0 → … → 2.7. A third component (e.g. 0.6.1) marks a patch within a minor version.

### Changelog

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
