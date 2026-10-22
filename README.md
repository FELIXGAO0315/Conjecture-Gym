# Conjecture-Gym

> **Infinite, verifiable conjectures for training mathematical reasoning in small LLMs.**

Conjecture-Gym is a data factory and reinforcement-learning environment that manufactures
mathematical conjectures which are **true, proved, and formally checked by the Lean 4 kernel**
— without any language model in the loop. Deduction is symbolic, truth is decided by exact
arithmetic, and every formalization is a deterministic translation with no `sorry`.

The point of the project is captured in one word: **infinite**. The supply of hard, structured,
machine-checkable theorems does not run out. This document explains *why* that is true — not as a
slogan, but as a property of the carriers the generator reasons over — and how the architecture is
built so the trajectory keeps extending indefinitely.

```
            axioms ──▶ forward deduction ──▶ candidate facts ──▶ Lean 4 kernel ──▶ record ──▶ RL env
         (symbolic)      (no LLM)            (filtered, scored)   (verify / reject)   (dataset)   (reward)
```

---

## Why this can be extended forever

A conjecture generator is only as inexhaustible as the space it draws from. Most "theorem
generators" quietly saturate: the underlying objects have finitely many invariants, so after a
while every new candidate is a disguised copy of an old one. We found this the hard way, and the
design that came out of it has **two independent axes of unboundedness**.

**Axis 1 — within a domain: carriers with no ceiling.**
A domain's *carrier* is the mathematical object it reasons about. Some carriers are finite in
disguise and some are genuinely open-ended:

- A **fixed graph** has only ~11 integer invariants (`n, m, χ, ω, α, …`). The space of
  linear-inequality theorems among them is large but **finite**, and our measurements show it
  *saturating* — yield per unit of search falls off sharply and difficulty stops climbing. This is
  an honest negative result, and it is *why* the project does not stop at graphs.
- The **free magma** — a single type with one binary operation and *no imposed relations* —
  is the opposite. Distinct terms stay distinct, so the space of equational terms grows without
  bound (roughly Catalan-many shapes × variable labelings), and it **never canonicalizes down to a
  fixed finite set**. Difficulty is simply *derivation length*: richer axiom sets and deeper terms
  produce longer proofs, with no ceiling. This is the engine room of the "infinite" claim.
- **Parametric families** (e.g. the complete graph `K_n`) yield `∀ n` statements — an entire
  class of theorems a single fixed object cannot even express.

**Axis 2 — across domains: a pluggable architecture.**
The engine is **domain-agnostic**. It knows how to saturate an axiom base, enumerate and filter
candidates, translate a proof to Lean, compile it, score it, and verify it fail-closed — *without
naming any subject-specific object*. A new mathematical subject becomes a new generator by
implementing one interface. The project ships five domains today; the sixth is a file, not a
rewrite.

Put together: each domain is a trajectory, the open-ended domains have no end, and the architecture
admits new trajectories forever. That is the sense in which Conjecture-Gym is infinitely extensible.

---

## The trust boundary

**Nothing counts unless the Lean 4 kernel accepts it.** The search and the generator are *untrusted*
— they may propose anything. A proposal becomes a record only if its generated `.lean` file compiles
with no `sorry` and depends only on the permitted axioms for its domain:

| Domain  | Standard axioms used                              | Notes |
|---------|---------------------------------------------------|-------|
| magma   | `propext`                                         | lightest footprint; finite counter-models checked by `decide` |
| graph   | `propext`, `Quot.sound`, `Classical.choice`       | the standard Mathlib trio |
| family  | `propext`, `Quot.sound`, `Classical.choice`       | parametric, over Mathlib graph theory |
| hex     | the trio **+** `sorryAx` (via its Inventory)      | frozen; excluded from the RL reward track for this reason |

Because verification is independent of generation, bugs in the (large, heuristic) search can never
produce a false theorem — at worst they waste compile time. This is what makes the records safe to
train on.

---

## The engine / domain architecture

Conjecture-Gym separates a reusable **engine** from the **domains** that plug into it.

```
PolyForge/
├── engine/                 # domain-agnostic BACKEND
│   ├── deducer.py          #   the "anvil": LP saturation, integer rounding, case splits, products
│   ├── generator.py        #   generic driver: cache, soundness, record IO, parallel workers
│   ├── formalizer.py       #   generic Lean compilation (single / batch, bisection)
│   ├── scoring/            #   hardness (proof cost) · iris + interestingness (GRAFFITI-style value)
│   └── soundness/          #   fail-closed verification KERNEL (Lean, canon, policies, batch)
├── domains/                # SUBJECTS — each plugs into the engine via domains/base.py
│   ├── base.py             #   the Domain interface (variables, inventory, sampling, Lean templates…)
│   ├── magma/              #   equational theories on the free magma  ← the infinite generator
│   ├── family/             #   parametric graph families (∀ n)
│   ├── graph/              #   graph-invariant inequalities (fixed carrier + full RL env)
│   └── hex/                #   p₆ of simple 3-polytopes (original HexForge; frozen)
├── lean/                   # shared Lean 4 + Mathlib v4.34.0 workspace (GraphLemmas; .lake git-ignored)
├── env/                    # RL ENVIRONMENT + DATASET (tasks, verifier, reward, evaluate, export)
├── scripts/                # cross-segment production driver
└── tests/                  # correctness guard rail (pytest)
```

A **domain** supplies everything subject-specific through a single interface: its variable set and
proved axiom base ("Inventory"), its premise sampling and proposition format, its filters, its Lean
statement/proof templates, and its dataset. The engine supplies everything else.

---

## The domains — the trajectory, extended

| Domain | Carrier | What it demonstrates | Verified records | Difficulty axis |
|--------|---------|----------------------|------------------|-----------------|
| **magma** | free magma (one binary op, no relations) | **genuinely infinite, non-saturating** | **39,000+** | derivation length (unbounded) |
| **family** | parametric `K_n` | an unbounded class (`∀ n`) the fixed carrier can't express | 96 | invariant coupling / breadth |
| **graph** | one finite simple graph | a rich but **finite** carrier + a complete RL env | 324 | proof structure (splits/products) |
| **hex** | simple 3-polytopes (p₆) | the original subject; reproduced byte-for-byte | 212 (frozen) | case-split depth |

### magma — the infinite generator

From an oriented axiom set (associativity, idempotence, projections, …), the generator enumerates
free-magma terms, **normalizes** each one, and emits every non-trivial consequence `∀ vars, t = nf(t)`
as a Lean theorem. Crucially, each theorem is proved **by its exact derivation path** — the
normalizer's rewrite steps become a `rw [...]` chain (with a `simp only` fallback) — so provability is
guaranteed even for non-confluent axiom sets. Every record is verified by a resident Mathlib REPL;
**all are provable, zero undecided**, with the lightest possible axiom footprint (`propext` only).

The result is a domain that does not saturate: it currently holds **39,155 Lean-verified equational
theorems** across 14 axiom-set × term-depth configurations, and the only limits are the term depth
and axiom richness you choose to enumerate. Difficulty rises with derivation length, and the free
magma imposes no relation that would ever collapse the space.

```lean
theorem assoc_idem {α : Type*} [Mul α]
    (h0 : ∀ a b c : α, (a * b) * c = a * (b * c)) (h1 : ∀ a : α, a * a = a) :
    ∀ a : α, a * a = a := by
  intro a
  first
  | rw [h1 a]
  | simp only [h0, h1]
```

### family — unbounded parametric classes

The fixed-graph domain can state facts about *a* graph; it cannot state `∀ n, ω(K_n) = n`. The family
domain does. It enumerates relations among the closed forms of a parametric family's invariants
(`ω = n`, `maxDeg = minDeg = n−1`, `edges = n(n−1)/2` for `K_n`) and emits each as a `∀ n ≥ 1` Lean
theorem, proved by a single validated scaffold (establish regularity + handshake, rewrite to closed
forms, close with `omega`/`nlinarith`). Each parametric theorem can be specialized to concrete
instances that cite it. New families simply register their invariant closed forms.

### graph — a rich finite carrier, and an honest ceiling

The graph domain generates linear (in)equalities among graph invariants under property premises,
proved over Mathlib's graph theory plus self-proved `GraphLemmas` (the Gallai identity `α + τ = n`,
handshake degree bounds, McCormick envelopes for product facts, Turán/Mantel conditionals with case
splits, …). It is the most feature-complete domain — canonical forms, redundancy/reverse-pruning to a
non-redundant basis, weakened-form promotion, degeneracy filtering — and it carries the project's full
RL environment.

It is also the domain that taught us where saturation lives. With only ~11 invariants the carrier is
finite, and measured yield falls off: raising the search budget buys almost nothing. **The graph
domain is not the infinite engine — it is the diagnosis that motivated building one.** It remains the
workhorse for *quality* and for the training stack, while magma and family carry *inexhaustibility*.

```
if ((min_deg >= 3)), then (2*m >= 3*n)
if ((is_tree) and (n >= 10)), then (m >= 9)
if ((not_bipartite)), then (chi >= 3)
```

### hex — the original subject, frozen

HexForge: lower bounds on `p₆` (hexagonal faces) of simple 3-connected planar maps, derived from
Euler's formula, Jucovič, and Barnette's bound. Kept unchanged as the first domain; its 212-conjecture
record is preserved and reproduced byte-for-byte. Because its Inventory uses `sorry`-as-axiom
placeholders for the deep theorems, it is excluded from the RL reward track.

---

## The forward pipeline

Every domain runs the same AlphaGeometry-style loop — sample premises, deduce forward, keep the
interesting conclusions, formalize, verify, score:

```
premises → anvil (deduction) → generator (selection) → formalizer (Lean) → scoring → record
```

1. The domain samples premises that at least one real object satisfies.
2. **anvil** derives new facts from the axiom base using linear combination, integer rounding, case
   split, and (for domains with product facts) a McCormick-envelope product step.
3. The domain keeps what it cares about, removes trivial/duplicate/decomposable/redundant
   conclusions, and extracts a minimal proof by traceback.
4. Each candidate is checked exactly, regression-tested on the domain's dataset, and translated to
   Lean. **Only conjectures whose `.lean` compiles (no `sorry`, standard axioms only) enter the
   record.**
5. **scoring** attaches a *hardness* score (proof cost / statement length) and an *interestingness*
   score (GRAFFITI-style: sharpness + tightness + breadth) — orthogonal signals, so a record can be
   easy-but-sharp or hard-but-loose.

---

## The RL training environment

Beyond generating conjectures, the project ships an executable RL environment (`PolyForge/env/`) so
the records can train and evaluate theorem-proving models directly. Scoring matches openai-math: a
proof earns **reward 1** iff its statement is exactly the reference statement, the Lean kernel accepts
it, and it depends only on the standard axioms — otherwise **0**.

- **Task format** (`env/tasks.py`) — each record becomes a task with a stable `task_id` (hash of the
  name-neutralized Lean statement), a fixed header + statement ending in `:= by`, a difficulty tier,
  and a reproducible train/test split grouped by skeleton.
- **Verifier** (`env/verifier.py`) — a resident Lean REPL (pinned `v4.34.0`) that loads Mathlib once
  and reuses it for every submission, with layered anti-cheating: a static scan (no top-level
  commands, `set_option`, `sorry`/`admit`), a compile check under heartbeat + wall-clock limits, an
  environment diff, an elaborated-type match against the cached reference, and a standard-axioms check.
  Any failing layer ⇒ reward 0.
- **Reward** (`env/reward.py`) — `reward_fn(task_ids, completions)` for TRL/verl; extracts the proof
  from the last ```` ```lean ```` block and calls the batched verifier.
- **Evaluation** (`env/evaluate.py`) — pass@1 / pass@k (unbiased estimator) over a predictions file,
  broken down by difficulty and split.
- **Export** (`env/export.py`) — writes `tasks/train/test.jsonl` (public rows carry **only** the
  problem statement and split), an SFT file, and metadata. Reference proofs and provenance stay
  server-side.

---

## Quickstart

```bash
# 1. Build the Lean + Mathlib workspace and the resident REPL (once)
bash PolyForge/env/setup_repl.sh

# 2. Generate — the infinite domain
python -m PolyForge.domains.magma.generator assoc,idem 4     # consequences of {assoc, idem}, depth 4
python -m PolyForge.domains.family.generator                 # ∀n theorems for the K_n family

# 3. Generate — the graph domain (full pipeline, parallel workers, Lean-verified)
python -m run polyforge graph 80                             # 80 hard conjectures, then an easy tier
python -m run polyforge graph --minutes 30                   # or run for a fixed budget

# 4. Train / evaluate
python -m PolyForge.env.export graph --out /tmp/graph_env
python -m PolyForge.env.evaluate graph predictions.jsonl --nprocs 2
```

Generation is reproducible: results are consumed in strict premise-index order, so the record is
independent of the worker count, and seeds/work-budgets make a segment a deterministic function of
`(seed, target, max_groups)`. Runs are crash-safe (atomic writes, an exclusive record lock, a
per-run write token, workers killed with the parent).

---

## Design principles

- **Verify, don't trust.** The kernel is the only authority; the generator is disposable.
- **No LLM in the manufacturing loop.** Deduction is symbolic and truth is exact, so the training
  data cannot be contaminated by the models it will train.
- **Quality is a filter, not an afterthought.** Redundancy pruning keeps each record a non-redundant
  basis; decomposability, degeneracy, and weakened-form filters remove padding; difficulty and
  interestingness are scored and separated.
- **Chase inexhaustibility where it actually lives.** Depth on a finite carrier is water; genuine
  difficulty and genuine breadth come from open-ended carriers (free magma) and new subjects (the
  pluggable engine). The architecture is built around this lesson.

---

## Roadmap — the trajectory continues

The engine/domain split means the natural next steps are *new carriers and deeper axis coverage*, not
rewrites:

- **magma**: scale term depth and axiom richness (the difficulty frontier is derivation length — it
  has no ceiling); add the implication/non-implication classification track (finite counter-models by
  `decide` + bounded proof search), isolating the genuinely-hard frontier the Equational Theories
  Project studies.
- **family**: more parametric families (cycles, paths, hypercubes, Turán graphs) with Mathlib-levered
  closed forms.
- **new domains**: any subject with a proved axiom base and a Lean formalization plugs in through
  `domains/base.py`.
- **training**: wire the magma and family records into the RL reward track alongside graph.

---

## Repository layout

```
Conjecture-Gym/
├── run.py                  # entry point:  python -m run polyforge <domain> …
├── README.md               # this file
├── requirements-dev.txt
└── PolyForge/
    ├── engine/             # domain-agnostic backend (deducer, generator, formalizer, scoring, soundness)
    ├── domains/            # magma · family · graph · hex   (each implements domains/base.py)
    ├── lean/               # shared Lean 4 + Mathlib v4.34.0 workspace
    ├── env/                # RL environment: tasks, verifier, reward, evaluate, export, analysis
    ├── scripts/            # production driver (reproducible multi-segment runs)
    └── tests/              # pytest correctness guard rail
```

---

## Versioning & history

Versions run `x.0 … x.7` then the major increments (`0.7 → 1.0 → … → 1.7 → 2.0`); a third component
(`1.4.2`) is a patch. Highlights:

- **v1.6** — the **magma** (infinite equational-theory) and **family** (parametric `∀ n`) domains;
  the `interestingness` scorer; the graph deliverable + export. The project becomes genuinely
  multi-carrier, with an open-ended generator at its center.
- **v1.5** — trust/release hardening on the graph record: dependency pins, run-state safety, a
  hardened verification kernel, two-sided derivation certificates, and an independent audit with no
  confirmed findings.
- **v1.4** — reverse pruning to a non-redundant basis regardless of discovery order; weakened forms
  promoted to their cleanest core; reproducible deterministic multi-segment production runs.
- **v1.3** — the executable RL environment: task format, batched Lean verifier with layered
  anti-cheating, reward function, pass@k evaluation, SFT export.
- **v1.2** — graph products as auxiliary variables with McCormick envelopes; handshake/edge/bipartite
  bounds; canonical forms modulo active identities.
- **v1.1** — the graph domain: linear Inventory from Mathlib + self-proved `GraphLemmas`, property
  premises, rotating primary invariant, redundancy checks.
- **v1.0** — renamed to PolyForge; the domain-agnostic engine + the `domains/` split; hex kept as the
  first domain.
- **v0.x** — the original HexForge: the end-to-end anvil → generator → Lean → scoring pipeline for p₆.

---

**In one line:** Conjecture-Gym turns axioms into Lean-proven theorems with no model in the loop,
over carriers chosen so the supply never runs out — a generator whose trajectory extends indefinitely.