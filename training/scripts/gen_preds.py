"""Generate proofs on the GPU box, where the base model + LoRA adapter live.

Loads base + model/ adapter (repo root), samples k proofs for each held-out test statement, and
writes training/scripts/preds.jsonl (statements + generated proofs).  Then score locally with
`python -m assess` (Lean-verified).  Resume-safe: re-running skips statements already in preds.jsonl.

    python training/scripts/gen_preds.py --n 100 --k 5
"""
import argparse, json
from pathlib import Path
import torch
from transformers import AutoModelForCausalLM, AutoTokenizer
from peft import PeftModel

HERE = Path(__file__).resolve().parent
BASE_DEFAULT = "Qwen/Qwen2.5-Coder-1.5B-Instruct"   # must match the base you fine-tuned
SYS = ("You are an expert Lean 4 theorem prover using Mathlib. "
       "Given a theorem statement, respond with ONLY the Lean proof that completes the `:=` "
       "(a term or a `by ...` tactic block), inside a ```lean code block.")

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=100)
    ap.add_argument("--k", type=int, default=1)
    ap.add_argument("--base", default=None, help="base model; auto-read from the adapter if omitted")
    ap.add_argument("--adapter", default=str(HERE.parents[1] / "model"))   # repo-root/model
    ap.add_argument("--out", default=str(HERE / "preds.jsonl"))
    ap.add_argument("--max-new-tokens", type=int, default=1024, dest="max_new_tokens",
                    help="cap on generated proof length (512 truncated most proofs — 1024 is safer)")
    ap.add_argument("--limit", type=int, default=0,
                    help="generate at most this many NEW statements this call (0 = all remaining); "
                         "enables resumable chunked runs")
    args = ap.parse_args()

    tests = [json.loads(l) for l in (HERE / "data" / "test.jsonl").read_text().splitlines() if l.strip()]
    tests = tests[:args.n]
    dev = "cuda" if torch.cuda.is_available() else "cpu"
    # resolve the base: explicit flag > the base the adapter was trained on > default
    adapter_ok = Path(args.adapter).exists()
    cfgp = Path(args.adapter) / "adapter_config.json"
    base = args.base or (json.loads(cfgp.read_text()).get("base_model_name_or_path") if cfgp.exists() else None) or BASE_DEFAULT
    print("base:", base)
    tok = AutoTokenizer.from_pretrained(base)
    model = AutoModelForCausalLM.from_pretrained(base, dtype="auto").to(dev)
    if adapter_ok:
        model = PeftModel.from_pretrained(model, args.adapter); print("adapter:", args.adapter)
    else:
        print("!! no adapter — generating from BASE model (baseline)")
    model.eval()

    def gen(statement):
        msgs = [{"role": "system", "content": SYS},
                {"role": "user", "content": f"Prove this Lean 4 theorem:\n\n```lean\n{statement} :=\n```"}]
        enc = tok.apply_chat_template(msgs, add_generation_prompt=True, return_tensors="pt",
                                      return_dict=True).to(dev)
        kw = dict(max_new_tokens=args.max_new_tokens, pad_token_id=tok.eos_token_id)
        if args.k > 1:
            kw.update(do_sample=True, temperature=0.7, top_p=0.95)
        out = model.generate(**enc, **kw)
        return tok.decode(out[0][enc["input_ids"].shape[1]:], skip_special_tokens=True)

    # RESUMABLE: skip statements already in preds.jsonl, append new ones one-by-one (flushed), so a
    # timeout only loses the current one — re-running continues from where it stopped.
    out = Path(args.out)
    done = set()
    if out.exists():
        done = {json.loads(l)["id"] for l in out.read_text().splitlines() if l.strip()}
    todo = [t for t in tests if t.get("id") not in done]
    if args.limit > 0:
        todo = todo[:args.limit]
    print(f"{len(done)}/{len(tests)} already done; generating {len(todo)} more this call", flush=True)
    with open(out, "a") as f:
        for j, t in enumerate(todo):
            gens = [gen(t["statement_lean"]) for _ in range(args.k)]
            f.write(json.dumps({"id": t.get("id"), "statement_lean": t["statement_lean"],
                                "proof_ref": t.get("proof_lean"), "gens": gens}, ensure_ascii=False) + "\n")
            f.flush()
            print(f"[{len(done)+j+1}/{len(tests)}] generated {t.get('id','')}", flush=True)
    total = len(done) + len(todo)
    # record the generation config in the adapter's run manifest (read by the assessment
    # to auto-fill the README training-report row)
    if adapter_ok:
        mp = Path(args.adapter) / "run_meta.json"
        meta = json.loads(mp.read_text()) if mp.exists() else {}
        meta.update({"base": base, "k": args.k, "max_new_tokens": args.max_new_tokens})
        mp.write_text(json.dumps(meta, indent=2))
    print(f"\npreds.jsonl now has {total}/{len(tests)}  →  {out}")

if __name__ == "__main__":
    main()
