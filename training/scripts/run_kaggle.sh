#!/usr/bin/env bash
# ============================================================================
#  Next nano-prover training run.  EDIT THIS FILE (then `git push`) to change the
#  next round — the fixed Kaggle cell just pulls the repo and runs this script, so
#  you never touch the notebook again.
# ============================================================================
set -e

# ----------------------------- CONFIG (run 3) -------------------------------
export SFT_MODEL='Qwen/Qwen2.5-Coder-3B-Instruct'   # bigger base; quick: '...1.5B...' / '...0.5B...'
export SFT_EPOCHS=2
export SFT_GRAD_CKPT=1        # gradient checkpointing (memory-safe)
export SFT_BATCH=1            # 3B on a T4: batch 1 ...
export SFT_GRAD_ACCUM=16     # ... × 16 accum = effective batch 16 (same as before)
export SFT_MAX_SEQ=1536      # don't truncate long proofs during training (was 1024)
export SFT_LORA_R=32         # bigger adapter (was 16)
GEN_N=100                    # held-out statements to evaluate
GEN_K=5                      # samples per problem -> pass@5
GEN_MAXTOK=1280              # generation length cap (run 2 still truncated 17% at 1024)
# ----------------------------------------------------------------------------

pip install -q -U transformers trl peft datasets accelerate
python training/scripts/prepare_data.py
python training/scripts/sft_train.py
python training/scripts/gen_preds.py --n "$GEN_N" --k "$GEN_K" --max-new-tokens "$GEN_MAXTOK"
echo "=== run_kaggle.sh done: training/scripts/preds.jsonl written ==="
