# Conjecture-Gym
Infinite Verifiable Conjectures for Training Mathematical Reasoning in Small LLMs

## HexForge (v0.6.3)

HexForge is the upstream data factory of Conjecture-Gym. Following the AlphaGeometry recipe, it samples random premises about simple 3-polytopes, runs a symbolic deduction engine forward, and turns the derived facts into new conjectures on p₆ — each one **true, proved, and formally verified in Lean 4** before it enters the record.

No LLM is used anywhere in the pipeline: deduction is symbolic, and Lean formalization is a deterministic translation of the deduction steps.

### Pipeline

```
premises → anvil (deduction) → generator (selection) → formalizer (Lean) → scoring → record
```

1. **generator** samples premises (e.g. `p_4 = 0`, `f_2 >= 7`) that at least one real polytope satisfies.
2. **anvil** derives new facts using the axiom base plus three inference actions: linear combination, integer rounding, and case split.
3. **generator** keeps conclusions involving p₆, removes trivial and duplicate ones, and extracts minimal proofs by traceback.
4. Every candidate is checked exactly, regression-tested on 25,190 real simple 3-polytopes, and translated to Lean. Only conjectures whose Lean file compiles are written to the record.
5. **scoring** attaches an IRIS score and a hardness score.

### Structure

```
Conjecture-Gym/
├── run.py                  # entry point
└── HexForge/
    ├── anvil/
    │   ├── inventory.py    # Python counterpart of Inventory.lean + HexLemmas.lean
    │   └── deducer.py      # inference actions, forward deduction, traceback
    ├── generator/          # premise sampling, selection, record writing
    ├── formalizer/         # proof steps → Lean, compile check
    ├── scoring/
    │   ├── iris.py         # IRIS: T + R + L
    │   └── hardness.py     # proof difficulty / statement length
    ├── lean/               # Inventory.lean (read-only), HexLemmas.lean
    ├── data/               # plantri_pool.json (real simple 3-polytopes)
    └── record/             # C{n}/C{n}.json, C{n}.md, C{n}.lean
```

### Usage

Run from the `Conjecture-Gym` root:

```bash
python -m run hexforge        # run until Ctrl+C
python -m run hexforge 50     # stop after 50 new conjectures
```

### Axiom base

All reasoning uses only the closed axiom base in `Inventory.lean` (Juc_EulerFormula, JucovicTheorem, Barnette_P6Bound) and elementary sum lemmas proved without `sorry` in `HexLemmas.lean`. `Inventory.lean` is never modified.

### Versioning

Each major version has eight minor versions, x.0 through x.7, after which the major version increments: 0.0 → … → 0.7 → 1.0 → … → 1.7 → 2.0 → … → 2.7. A third component (e.g. 0.6.1) marks a patch within a minor version.

### Changelog

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
