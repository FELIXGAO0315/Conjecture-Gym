"""Generate proofs on the GPU box (Colab), where the base model + LoRA adapter live.

Loads base + training/out/ adapter, samples k proofs for each held-out test statement, and
writes training/preds.jsonl — a SMALL text file (statements + generated proofs).  Push that
back (it's tiny, no 100 MB issue); the Lean-verified scoring runs locally via verify_preds.py.

    python training/gen_preds.py --n 100 --k 1
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
    ap.add_argument("--adapter", default=str(HERE / "out"))
    ap.add_argument("--out", default=str(HERE / "preds.jsonl"))
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
        kw = dict(max_new_tokens=512, pad_token_id=tok.eos_token_id)
        if args.k > 1:
            kw.update(do_sample=True, temperature=0.7, top_p=0.95)
        out = model.generate(**enc, **kw)
        return tok.decode(out[0][enc["input_ids"].shape[1]:], skip_special_tokens=True)

    with open(args.out, "w") as f:
        for i, t in enumerate(tests):
            gens = [gen(t["statement_lean"]) for _ in range(args.k)]
            f.write(json.dumps({"id": t.get("id"), "statement_lean": t["statement_lean"],
                                "proof_ref": t.get("proof_lean"), "gens": gens}, ensure_ascii=False) + "\n")
            print(f"[{i+1}/{len(tests)}] generated {t.get('id','')}")
    print(f"\nwrote {len(tests)} rows → {args.out}  (push this small file back; verify locally)")

if __name__ == "__main__":
    main()
