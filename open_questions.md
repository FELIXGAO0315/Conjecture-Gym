# Open Questions

Research questions parked for discussion (e.g. with the advisor). Each is stated with the
concrete evidence that raised it, so it can be argued from data, not intuition.

---

## Q1 (primary) — Can a nano-prover *learn a proof paradigm* from very few unique examples, or is this a hard few-shot-generalization wall?

**Context.** Conjecture-Gym's upstream (PolyForge v3.0) added a **structural** conjecture
carrier so the downstream nano-prover (a 1.5B LoRA-SFT'd code LLM) would see proof techniques
beyond the single `linarith`-style certificate that dominates the linear-inequality corpus.
Structural theorems split into two kinds:

- **instance paradigms** — a family × invariant closed form, instanced over many sizes
  (e.g. `(⊤ : SimpleGraph (Fin k)).cliqueNum = k` for `k = 3..40`). Each paradigm has
  **~38 unique examples** (size-varied).
- **deep paradigms** — predicate implications / equivalences / monotonicities / cited deep
  theorems (e.g. `IsTree → Connected`, `χ ≤ 2 ↔ IsBipartite`, Tutte's 1-factor theorem).
  These are **inventory-bound: only ~1–3 unique examples per paradigm**, because Mathlib
  contains only so many genuinely-distinct machine-provable structural facts.

**Experiment (v0.6).** We stratified the held-out set so deep paradigms were *measurable*
(40% of deep → test) and **upsampled the deep training rows 15×** so the model would see each
paradigm many times. Per-paradigm Lean-verified `pass@3` on the held-out set:

| class | pass@3 | note |
|---|---|---|
| structural **instance** | **30/31 = 97%** | generalizes — learned the technique |
| structural **deep** | **1/14 = 7%** | failed — only the trivial `fun h => h.1` case passed |
| LP harvest (linear ineq.) | 104/296 = 35% | (same 1.5B · 1 epoch) |

Deep, per paradigm: `iff.mp` 0/4, `iff cite` 0/2, `iff.mpr` 0/2, `tree edge count` 0/2,
`matching→parity` 0/1, `monotone (graph order)` 0/1, `destructure` 0/1; only
`implication (destructure/cite)` 1/1.

**The finding.** **Upsampling did not work.** Repeating the ~21 deep training theorems 15×
produced *memorization* of those specific statements, but the model could not prove the 14
*held-out* deep theorems (different statements, same paradigms). Instance paradigms, which
have genuine size-variation, generalize (97%); deep paradigms, with ~2 unique examples each,
do not (7%).

**The question for discussion.**
1. Is "learn a proof technique from ~2 unique examples" a **fundamental few-shot limit** at
   this model scale, or an artifact we can defeat with better method (curriculum, retrieval
   augmentation / in-context exemplars, meta-learning, a bigger base)?
2. Instance paradigms generalize *because of size-variation*. Is the right lever therefore to
   **manufacture variation** for deep paradigms rather than repeat them — and if so, how (see Q2)?
3. Is repetition (upsampling) simply the wrong tool for teaching rare, structurally-distinct
   skills, and what is the right one?

---

## Q2 — How do we manufacture *genuine variety* in deep structural theorems?

The scarcity in Q1 is upstream: Mathlib exposes a limited set of distinct structural lemmas,
and forward-composition of them (implication chains, iff projections, monotonicity transfers)
only multiplies so far before the results become trivial or redundant. Candidate levers, each
with an open cost/benefit:

- **(B) Formalize new deep lemmas ourselves** into `GraphLemmas.lean` (as was done for the ν/γ/κ
  invariants), giving the engine more *unique* deep inventory to compose. Genuine but
  research-formalization-heavy; which lemmas give the best coverage-per-effort?
- **Parametrize deep facts over families/sizes** the way instance facts are parametrized — but
  deep facts are `∀ G` (universally quantified); is there a construction that yields many
  *distinct, non-trivial* deep theorems with shared structure?
- **Accept the ceiling** and treat deep structural proving as out of reach at nano scale.

---

## Q3 — Is "proving deep structural theorems" even the right frontier, vs. *generating* open conjectures?

v3.0 also added an **empirical carrier** (`empirical.py`): it *generates* Barnette-level
conjectures (`class → structural conclusion`, e.g. `bipartite ∧ cubic → Hamiltonian`), screens
them for falsification against an enlarged graph pool (hard graphs + sampling to n = 46), and
keeps the unproven survivors (→ `output/open_conjectures.jsonl`). These are genuinely open /
hard — provability is not required, only non-falsifiability + irredundancy.

The north star is *conjecture quality/difficulty*, not prover accuracy. Given Q1's result that
deep **provable** structural theorems are hard to both teach and even obtain, is the higher-value
use of effort the **conjecture-generation** track (unproven, Barnette-level) rather than pushing
the prover to close deep proofs it has too few examples to learn? What is the right success
metric for a conjecture *generator* as opposed to a theorem *prover*?

---

### Status / what's already established

- Measurement is clean: the assessment now reports **pass@k per proof method**, so these
  per-paradigm numbers are directly observable each run (not inferred).
- Instance structural paradigms (~14 distinct non-`linarith` techniques) **are learned** (97%) —
  that part of the diversification goal succeeded.
- Deep structural paradigms are **not** learned via upsampling (7%); the bottleneck is unique-example
  scarcity, which is upstream (Mathlib) and not fixed by training-side tricks.
