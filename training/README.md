# nano-prover training

Fine-tune a small LLM to prove the graph-theory theorems in `output/train_corpus.jsonl`
(input = Lean statement, output = Lean proof). Portable: GPU or CPU.

```
prepare_data.py  →  sft_train.py  →  (download adapter)  →  eval_lean.py
   split corpus      LoRA SFT          to local repo          Lean-verified pass@k
```

## Workflow (local dev → Posit Workbench training → local eval)

1. **Local (this machine):** commit + push the repo (the corpus `output/train_corpus.jsonl`
   is included). The Lean verifier stays here for evaluation.

2. **On Workbench** (JupyterLab or VS Code session — pick a **GPU** resource profile if one
   is offered; CPU works but is slow, use the 0.5B model then):
   ```bash
   git pull
   # GPU session: install a CUDA torch first, e.g.
   #   pip install torch --index-url https://download.pytorch.org/whl/cu121
   pip install -r training/requirements.txt
   python training/prepare_data.py          # → training/data/{train,test}.jsonl
   python training/sft_train.py             # → training/out/ (LoRA adapter)
   ```
   Then commit/push `training/out/` (or download it) back.

3. **Local:** pull the adapter, then run the Lean-verified evaluation:
   ```bash
   git pull
   python training/eval_lean.py --n 50 --k 1   # real pass@k via the Mathlib REPL
   ```

## Model choice

- Default: **Qwen/Qwen2.5-Coder-1.5B-Instruct** (T4 / 12 GB-class GPU friendly, knows Lean).
- CPU-only or fast iteration: set `MODEL` to **Qwen/Qwen2.5-Coder-0.5B-Instruct** in
  `sft_train.py` (and `--base` in `eval_lean.py`).
- Bigger GPU (24 GB+): try 3B, or the domain-specialized **DeepSeek-Prover-V2-7B** as the base.

## Notes

- Loss is computed on the proof only (`assistant_only_loss`), not the prompt.
- `eval_lean.py` is the *only* honest metric here: a proof counts iff the Lean 4 kernel
  accepts it (no `sorry`, standard axioms) — not string match against the reference.
- 5.6k examples is small; LoRA SFT teaches the proof *style/format*. Scale the corpus
  (more `python -m run graph` runs / more parametric families) before expecting hard wins.
