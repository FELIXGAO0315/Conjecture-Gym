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

SYS = ("You are an expert Lean 4 theorem prover using Mathlib. "
       "Given a theorem statement, respond with ONLY the Lean proof that completes the `:=` "
       "(a term or a `by ...` tactic block), inside a ```lean code block.")

def user_prompt(statement_lean: str) -> str:
    return f"Prove this Lean 4 theorem:\n\n```lean\n{statement_lean} :=\n```"

def main():
    rows = [json.loads(l) for l in CORPUS.read_text().splitlines() if l.strip()]
    rows = [r for r in rows if r.get("statement_lean") and r.get("proof_lean")]
    random.Random(SEED).shuffle(rows)
    n_test = max(1, int(len(rows) * TEST_FRACTION))
    test, train = rows[:n_test], rows[n_test:]
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
                                "statement_lean": r["statement_lean"],
                                "proof_lean": r["proof_lean"],
                                "difficulty": r.get("difficulty")}, ensure_ascii=False) + "\n")

    print(f"corpus {len(rows)} → train {len(train)}  test {len(test)}  → {OUT}/")

if __name__ == "__main__":
    main()
