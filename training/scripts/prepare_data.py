"""Turn output/train_corpus.jsonl into SFT train/test files for a nano Lean prover.

Each corpus row is (statement_lean = PROBLEM, proof_lean = TARGET).  We build an
instruction sample: the model is shown the theorem signature (up to `:=`) and must
produce the proof.  Train rows are chat messages (user→assistant); test rows keep the
raw statement/proof so the local Lean verifier can check generated proofs.

Run from the repo root:
    python training/scripts/prepare_data.py
Writes training/scripts/data/train.jsonl and training/scripts/data/test.jsonl.
"""
import json, random
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
CORPUS = ROOT / "output" / "train_corpus.jsonl"
OUT = Path(__file__).resolve().parent / "data"
TEST_FRACTION = 0.05
SEED = 0

# ── deep structural paradigms are SCARCE (~tens, ~2 per paradigm): a plain 5% split barely
# samples them, so they are neither learnable nor measurable.  We treat them specially:
#   · stratify — force a fixed fraction into test so each paradigm gets eval coverage;
#   · upsample — repeat the deep TRAIN rows so the model sees each paradigm many times.
# (The abundant `structural instance` paradigms already have size-variation, so they go
# through the normal split.)
DEEP_TEST_FRACTION = 0.40    # fraction of deep-structural held out for measurement
DEEP_UPSAMPLE = 15           # repeat each deep-structural TRAIN row this many times

def is_deep_structural(r):
    return (r.get("domain") == "graph-structural"
            and r.get("conjecture_type") != "structural instance")

SYS = ("You are an expert Lean 4 theorem prover using Mathlib. "
       "Given a theorem statement, respond with ONLY the Lean proof that completes the `:=` "
       "(a term or a `by ...` tactic block), inside a ```lean code block.")

def user_prompt(statement_lean: str) -> str:
    return f"Prove this Lean 4 theorem:\n\n```lean\n{statement_lean} :=\n```"

def main():
    rows = [json.loads(l) for l in CORPUS.read_text().splitlines() if l.strip()]
    rows = [r for r in rows if r.get("statement_lean") and r.get("proof_lean")]
    rng = random.Random(SEED)

    # split deep-structural separately (stratified), everything else by the normal fraction
    deep = [r for r in rows if is_deep_structural(r)]
    rest = [r for r in rows if not is_deep_structural(r)]
    rng.shuffle(deep); rng.shuffle(rest)
    n_deep_test = max(1, int(len(deep) * DEEP_TEST_FRACTION)) if deep else 0
    deep_test, deep_train = deep[:n_deep_test], deep[n_deep_test:]
    n_rest_test = max(1, int(len(rest) * TEST_FRACTION))
    rest_test, rest_train = rest[:n_rest_test], rest[n_rest_test:]

    test = deep_test + rest_test
    train = deep_train * DEEP_UPSAMPLE + rest_train      # upsample deep (no test leakage: disjoint)
    rng.shuffle(train); rng.shuffle(test)
    OUT.mkdir(parents=True, exist_ok=True)

    with open(OUT / "train.jsonl", "w") as f:
        for r in train:
            f.write(json.dumps({"messages": [
                {"role": "system", "content": SYS},
                {"role": "user", "content": user_prompt(r["statement_lean"])},
                {"role": "assistant", "content": f"```lean\n{r['proof_lean']}\n```"},
            ]}, ensure_ascii=False) + "\n")

    with open(OUT / "test.jsonl", "w") as f:            # raw fields for Lean-verified eval
        for r in test:
            f.write(json.dumps({"id": r.get("id"), "source": r.get("source"),
                                "conjecture_type": r.get("conjecture_type"),
                                "tactics": r.get("tactics"),
                                "statement_lean": r["statement_lean"],
                                "proof_lean": r["proof_lean"],
                                "difficulty": r.get("difficulty")}, ensure_ascii=False) + "\n")

    print(f"corpus {len(rows)} → train {len(train)} "
          f"(deep {len(deep_train)}×{DEEP_UPSAMPLE}={len(deep_train)*DEEP_UPSAMPLE} upsampled) "
          f"test {len(test)} (deep {len(deep_test)})  → {OUT}/")

if __name__ == "__main__":
    main()
