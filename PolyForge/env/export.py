"""PolyForge dataset export & train/test split (v1.3 §VI).

``python -m PolyForge.env.export graph --out <dir>`` reads the current ``graph``
records and writes a self-contained RL-environment dataset:

  tasks.jsonl        every task, PUBLIC fields only (statement + split; no answer)
  train.jsonl        the training split (public fields)
  test.jsonl         the test split (public fields)
  sft_train.jsonl    SFT pairs for the training split (prompt / completion) — server-side
  task_record_map.server.jsonl  task_id -> record (C{n}) linkage — server-side only
  metadata.json      versions, difficulty thresholds, counts, split rule & seed
  README.md          English description of the environment and its usage

The split groups tasks by skeleton (no skeleton straddles the split) and sends a
whole group to test with a probability set by its hardest tier, decided by the
skeleton hash so the result is reproducible.  Products are written outside the
repo (pass an ``--out`` directory that is not tracked by git).
"""

from __future__ import annotations

import argparse
import json
import re
from collections import Counter, defaultdict
from pathlib import Path

from . import tasks as T
from . import ENV_VERSION
from .verifier import (DEFAULT_MAX_HEARTBEATS, DEFAULT_TIMEOUT, STANDARD_AXIOMS,
                       default_nprocs)

_REPL_COMMIT = "193cf4bb9a22bb3fc6d25774f0fe6a70db1fd6ee"   # tag v4.34.0
_REPL_TAG = "v4.34.0"
_DEFAULT_SPLIT_SEED = 1337


def _lean_versions(cfg: T.DomainConfig) -> dict:
    tc = (cfg.lean_dir / "lean-toolchain")
    lean = tc.read_text().strip() if tc.exists() else "unknown"
    mathlib = "unknown"
    man = cfg.lean_dir / "lake-manifest.json"
    if man.exists():
        data = json.loads(man.read_text())
        for pkg in data.get("packages", []):
            if pkg.get("name") == "mathlib":
                mathlib = pkg.get("inputRev") or pkg.get("rev", "unknown")
    return {"lean_toolchain": lean, "mathlib": mathlib}


def _sft_prompt(task: dict) -> str:
    return (
        f"{task['natural_language']}\n\n"
        f"Lean statement:\n```lean\n{task['lean_header']}\n\n{task['lean_statement']}\n```\n\n"
        "Give the proof that goes after `by` in a ```lean code block."
    )


def _sft_record(task: dict) -> dict:
    return {
        "task_id": task["task_id"],
        "prompt": _sft_prompt(task),
        "completion": f"```lean\n{task['reference_proof']}\n```",
        "natural_language_proof": task["natural_language_proof"],
    }


def export(domain: str, out_dir: Path, split_seed: int = _DEFAULT_SPLIT_SEED) -> dict:
    cfg = T.domain_config(domain)
    out_dir.mkdir(parents=True, exist_ok=True)
    tasks = T.build_tasks(domain, split_seed=split_seed)

    # collision guard across the whole export (tasks.build_tasks already checks,
    # but we assert the id set size matches)
    ids = [t.task_id for t in tasks]
    if len(set(ids)) != len(ids):
        dup = [i for i, c in Counter(ids).items() if c > 1]
        raise RuntimeError(f"task_id collision on export: {dup}")

    hardness = [t.hardness for t in tasks]
    t1, t2 = T.difficulty_thresholds(hardness)

    train = [t for t in tasks if t.split == "train"]
    test = [t for t in tasks if t.split == "test"]

    T.dump_jsonl(tasks, out_dir / "tasks.jsonl")
    T.dump_jsonl(train, out_dir / "train.jsonl")
    T.dump_jsonl(test, out_dir / "test.jsonl")
    with open(out_dir / "sft_train.jsonl", "w") as f:
        for t in train:
            f.write(json.dumps(_sft_record(t.to_dict()), ensure_ascii=False, sort_keys=True) + "\n")

    # v1.5.1 §D3: SERVER-SIDE ONLY task_id -> record (C{n}) + generator version
    # mapping.  Never ship this to a model: it links the neutralised task_id back
    # to the record, which is where the answer lives.  Consumers that need the
    # answer (oracle_check, SFT) read it from record/ via build_tasks; this file
    # just persists the linkage that the removed public `source` field used to
    # carry.  (sft_train.jsonl likewise is server-side: it contains proofs.)
    with open(out_dir / "task_record_map.server.jsonl", "w") as f:
        for t in tasks:
            f.write(json.dumps({"task_id": t.task_id, "record": t.source["record"],
                                "generator_version": t.source["generator_version"]},
                               ensure_ascii=False, sort_keys=True) + "\n")

    # split statistics
    tier_split = defaultdict(lambda: Counter())
    for t in tasks:
        tier_split[t.difficulty][t.split] += 1
    n_skeletons = len({t.skeleton for t in tasks})

    metadata = {
        "env_version": ENV_VERSION,
        "domain": domain,
        "generator_version": tasks[0].source["generator_version"] if tasks else None,
        "lean": _lean_versions(cfg),
        "repl": {"repo": "leanprover-community/repl", "tag": _REPL_TAG, "commit": _REPL_COMMIT},
        "verifier_defaults": {
            "max_heartbeats": DEFAULT_MAX_HEARTBEATS,
            "timeout_seconds": DEFAULT_TIMEOUT,
            "standard_axioms": sorted(STANDARD_AXIOMS),
            "default_nprocs": default_nprocs(),
            "repl_header": cfg.repl_preamble,
        },
        "difficulty": {
            "metric": "hardness",
            "rule": "tertiles: easy = h<=t1, medium = t1<h<=t2, hard = h>t2",
            "thresholds": {"t1": round(t1, 6), "t2": round(t2, 6)},
            "counts": dict(Counter(t.difficulty for t in tasks)),
        },
        "split": {
            "rule": ("group by skeleton; a whole group -> test with probability by "
                     "its hardest tier (hard 0.4, medium 0.2, easy 0.1), decided by "
                     "the skeleton hash"),
            "seed": split_seed,
            "n_skeletons": n_skeletons,
            "counts": {"train": len(train), "test": len(test)},
            "test_ratio": round(len(test) / len(tasks), 4) if tasks else 0.0,
            "per_tier": {d: dict(tier_split[d]) for d in ("easy", "medium", "hard")},
        },
        "n_tasks": len(tasks),
        "license": "See the repository root README; records are PolyForge-generated "
                   "and derive only from Mathlib's proved theorems and self-proved GraphLemmas.",
    }
    (out_dir / "metadata.json").write_text(json.dumps(metadata, indent=2, ensure_ascii=False))
    (out_dir / "README.md").write_text(_readme(domain, metadata))
    return metadata


def _readme(domain: str, md: dict) -> str:
    t1 = md["difficulty"]["thresholds"]["t1"]
    t2 = md["difficulty"]["thresholds"]["t2"]
    cnt = md["difficulty"]["counts"]
    sp = md["split"]["counts"]
    return f"""# PolyForge {domain} training environment (v{md['env_version']})

This dataset is an executable RL environment built from PolyForge's record of
machine-generated, Lean-verified graph-theory conjectures. Every task is a true
theorem together with a formal statement in Lean 4; the goal is to produce a Lean
proof that the kernel accepts using only the standard axioms.

## What a task is

Each line of `tasks.jsonl` is one task. The task rows carry ONLY the problem
statement and split — no answer and no proof-strategy metadata (§D3):

- `task_id` — `{domain}-<12 hex>`, the hash of the (name-neutralised, whitespace-
  normalised) Lean statement. Stable across exports; the same statement always
  gets the same id.
- `domain`.
- `formula`, `canonical_form`, `natural_language` — the conjecture in PolyForge's
  notation, its identity-canonical form, and an English statement.
- `lean_header` — the `import`/`open` block.
- `lean_statement` — the theorem signature ending in `:= by` (no proof). The
  theorem is named `thm_<12 hex>` (never the record id).
- `hardness`, `iris` — scalar difficulty/interest scores (no proof structure).
- `split` — `train` or `test`.

The reference proof, natural-language proof, inventory used, depth_type,
proof_stats, the skeleton split key, the difficulty tier, the originating record
id and the theorem's record name are **not** in the task rows. They live
server-side only (in `record/`, reconstructable via `build_tasks`). SFT pairs
(with proofs) are in the separate server-side `sft_train.jsonl`; the task_id→record
linkage is in the separate server-side `task_record_map.server.jsonl`. Neither is
meant to be shown to a model.

## Submission & proof-extraction

A submission is **only the proof** — the tactic block that goes after `by`. The
verifier indents it and appends it to the fixed `lean_header` and `lean_statement`,
so a submitter cannot alter the statement.

For free-form model output, the reward function extracts the proof as follows:

1. take the content of the **last** ```` ```lean ```` fenced code block in the
   completion;
2. if it begins with `by`, drop that leading `by`;
3. if there is no ```` ```lean ```` block, reward is 0 (`no_proof_found`).

## Reward & anti-cheating

Reward is 1 iff **all** of the following hold, else 0 (matching openai-math):

- the statement is exactly the reference statement (the verifier controls it);
- no forbidden content (static scan): no top-level commands, `set_option`,
  `sorry`/`admit`, `#`-commands;
- the proof compiles (no leftover `sorry`), within the heartbeat and wall-clock
  limits;
- the proof adds no constants other than the target theorem (environment diff);
- the proved type equals the reference statement's elaborated type;
- the proof depends only on the standard axioms {sorted(STANDARD_AXIOMS)}.

Statuses: `ok`, `forbidden`, `compile_error`, `heartbeats`, `timeout`,
`env_modified`, `statement_mismatch`, `bad_axioms`, `no_proof_found`.

## Using the verifier and reward function

```python
from PolyForge.env.verifier import Verifier
V = Verifier("{domain}", nprocs=4)
res = V.verify(task_id, proof_string)        # res.reward, res.status, res.elapsed
results = V.verify_batch([(task_id, proof), ...])

from PolyForge.env.reward import reward_fn
rewards = reward_fn(task_ids, completions, domain="{domain}", nprocs=4)
```

Command line:

```bash
python -m PolyForge.env.verifier {domain} --task <task_id> --proof proof.lean
python -m PolyForge.env.verifier {domain} --batch submissions.jsonl
```

The verifier runs a resident Lean REPL (leanprover-community/repl, tag
`{md['repl']['tag']}`, commit `{md['repl']['commit']}`) that loads Mathlib and the
domain's Lean library once and reuses that environment for every submission. Build
it with `PolyForge/env/setup_repl.sh`.

## Evaluation

```bash
python -m PolyForge.env.evaluate {domain} predictions.jsonl --nprocs 4
```

`predictions.jsonl` has one object per line, `{{"task_id", "completions": [...]}}`.
The script reports pass@1 and pass@k (unbiased estimator) overall and by difficulty
tier and by split, plus the status distribution.

## Difficulty tiers

By hardness tertiles over all {md['n_tasks']} tasks: easy = h ≤ {t1}, medium =
{t1} < h ≤ {t2}, hard = h > {t2}. Counts: easy {cnt.get('easy',0)}, medium
{cnt.get('medium',0)}, hard {cnt.get('hard',0)}.

## Split

Grouped by `skeleton` (same skeleton never straddles train/test). Each group goes
to test with a probability set by its hardest tier (hard 0.4, medium 0.2, easy
0.1), decided by `sha256(seed:skeleton)` with seed {md['split']['seed']}. Result:
train {sp['train']}, test {sp['test']} (test ratio {md['split']['test_ratio']}).

## Source & license

Generated by PolyForge (generator version {md['generator_version']}). Lean
toolchain `{md['lean']['lean_toolchain']}`, Mathlib `{md['lean']['mathlib']}`. The
conjectures derive only from Mathlib's proved theorems and PolyForge's self-proved
`GraphLemmas` (no `sorry`). See the repository root for licensing.
"""


def _main(argv=None):
    ap = argparse.ArgumentParser(description="PolyForge dataset export")
    ap.add_argument("domain")
    ap.add_argument("--out", required=True, help="output directory (keep outside the repo)")
    ap.add_argument("--seed", type=int, default=_DEFAULT_SPLIT_SEED)
    args = ap.parse_args(argv)
    md = export(args.domain, Path(args.out), split_seed=args.seed)
    print(json.dumps(md, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    _main()
