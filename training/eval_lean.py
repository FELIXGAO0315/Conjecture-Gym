"""Lean-VERIFIED evaluation of the fine-tuned nano prover — real pass@k, not string match.

For each held-out test statement, sample k proofs from the model, reconstruct the full
theorem, and compile each through the resident Mathlib REPL (PolyForge/env/verifier.py).
A statement counts as solved if ANY of its k samples compiles (no `sorry`, standard axioms).

Runs LOCALLY (the Lean workspace + REPL live here).  CPU inference is fine for a sample:
    python training/eval_lean.py --n 50 --k 1
After training on Workbench, download training/out/ (the adapter) back into the repo first.
"""
import argparse, json, re, sys
from pathlib import Path
from types import SimpleNamespace

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
HERE = Path(__file__).resolve().parent

import torch
from transformers import AutoModelForCausalLM, AutoTokenizer
from peft import PeftModel
from PolyForge.env.verifier import ReplProcess, _REPL_BIN_DEFAULT

BASE = "Qwen/Qwen2.5-Coder-1.5B-Instruct"       # must match sft_train.MODEL
ADAPTER = HERE / "out"
LEAN = ROOT / "PolyForge" / "lean"
SYS = ("You are an expert Lean 4 theorem prover using Mathlib. "
       "Given a theorem statement, respond with ONLY the Lean proof that completes the `:=` "
       "(a term or a `by ...` tactic block), inside a ```lean code block.")

def extract_proof(text: str) -> str:
    m = re.search(r"```lean\s*(.*?)```", text, re.S)
    return (m.group(1) if m else text).strip()

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=50, help="how many test statements")
    ap.add_argument("--k", type=int, default=1, help="samples per statement (pass@k)")
    ap.add_argument("--base", default=BASE)
    ap.add_argument("--adapter", default=str(ADAPTER))
    args = ap.parse_args()

    tests = [json.loads(l) for l in (HERE / "data" / "test.jsonl").read_text().splitlines() if l.strip()]
    tests = tests[:args.n]

    dev = "cuda" if torch.cuda.is_available() else "cpu"
    tok = AutoTokenizer.from_pretrained(args.base)
    model = AutoModelForCausalLM.from_pretrained(args.base, torch_dtype="auto").to(dev)
    if Path(args.adapter).exists():
        model = PeftModel.from_pretrained(model, args.adapter)
        print(f"loaded adapter: {args.adapter}")
    else:
        print(f"!! no adapter at {args.adapter} — evaluating the BASE model (baseline)")
    model.eval()

    proc = ReplProcess(SimpleNamespace(lean_dir=LEAN, repl_preamble="import Mathlib"),
                       _REPL_BIN_DEFAULT, restart_every=10 ** 9)

    def verifies(statement, proof):
        cmd = "open SimpleGraph Finset\n\n" + statement + " := " + proof
        try:
            r = proc._send({"cmd": cmd, "env": proc.env0}, timeout=40)
        except Exception:
            return False
        if any(m.get("severity") == "error" for m in (r.get("messages") or [])):
            return False
        return not r.get("sorries")

    def gen(statement):
        msgs = [{"role": "system", "content": SYS},
                {"role": "user", "content": f"Prove this Lean 4 theorem:\n\n```lean\n{statement} :=\n```"}]
        enc = tok.apply_chat_template(msgs, add_generation_prompt=True, return_tensors="pt",
                                      return_dict=True).to(dev)
        kw = dict(max_new_tokens=512, pad_token_id=tok.eos_token_id)
        if args.k > 1:
            kw.update(do_sample=True, temperature=0.7, top_p=0.95)
        out = model.generate(**enc, **kw)
        return extract_proof(tok.decode(out[0][enc["input_ids"].shape[1]:], skip_special_tokens=True))

    solved = 0
    for i, t in enumerate(tests):
        ok = False
        for _ in range(args.k):
            if verifies(t["statement_lean"], gen(t["statement_lean"])):
                ok = True; break
        solved += ok
        print(f"[{i+1}/{len(tests)}] {'PASS' if ok else 'fail'}  {t.get('id','')}  {t['statement_lean'][:60]}")
    proc.stop()
    print(f"\npass@{args.k} = {solved}/{len(tests)} = {100*solved/len(tests):.1f}%")

if __name__ == "__main__":
    main()
