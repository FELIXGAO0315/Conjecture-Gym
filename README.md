# Conjecture-Gym
Infinite Verifiable Conjectures for Training Mathematical Reasoning in Small LLMs

## PolyForge (v1.0)

PolyForge is the upstream data factory of Conjecture-Gym. Following the AlphaGeometry recipe, it samples random premises about a mathematical subject, runs a symbolic deduction engine forward, and turns the derived facts into new conjectures — each one **true, proved, and formally verified in Lean 4** before it enters the record.

No LLM is used anywhere in the pipeline: deduction is symbolic, truth is decided only by exact arithmetic, and Lean formalization is a deterministic translation of the deduction steps (no `sorry`).

### Framework and domains

PolyForge separates a **domain-agnostic engine** from the **domains** that plug into it:

- The engine (`anvil`, `generator`, `formalizer`, `scoring`) knows how to saturate a closed linear axiom base, enumerate and filter candidate conclusions, translate a proof to Lean and compile it, and score the result — without naming any subject-specific object.
- A **domain** supplies everything subject-specific through a single interface (`domains/base.py`): its variable set and Inventory (proved axiom base), its premise sampling and proposition format, its filters, its Lean statement/proof templates, its IRIS features, and its dataset.

This version ships two domains:

- **hex** — the original HexForge subject: p₆ of simple 3-connected planar maps (simple 3-polytopes). Fully wired and unchanged from v0.7; the 212-conjecture record is preserved and reproduced byte-for-byte.
- **graph** — a skeleton for the next stage (graph theory on top of Mathlib's proved graph theorems). It has its own Lean project (recent Mathlib) and a graph dataset, but does not yet generate conjectures.

### Pipeline

```
premises → anvil (deduction) → generator (selection) → formalizer (Lean) → scoring → record
```

1. The domain samples premises that at least one dataset object satisfies.
2. **anvil** derives new facts from the domain's axiom base using three inference actions: linear combination, integer rounding, and case split.
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

### Versioning

Each major version has eight minor versions, x.0 through x.7, after which the major version increments: 0.0 → … → 0.7 → 1.0 → … → 1.7 → 2.0 → … → 2.7. A third component (e.g. 0.6.1) marks a patch within a minor version.

### Changelog

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
