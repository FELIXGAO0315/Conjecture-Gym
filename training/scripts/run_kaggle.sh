#!/usr/bin/env bash
# ============================================================================
#  Next nano-prover training run.  EDIT THIS FILE (then `git push`) to change the
#  next round — the fixed Kaggle cell just pulls the repo and runs this script, so
#  you never touch the notebook again.
# ============================================================================
set -e

# ----------------------------- CONFIG ---------------------------------------
export SFT_MODEL='Qwen/Qwen2.5-Coder-1.5B-Instruct'   # quick run: '...Qwen2.5-Coder-0.5B-Instruct'
export SFT_EPOCHS=3
export SFT_GRAD_CKPT=1        # 1 = gradient checkpointing on (safer memory for 1.5B on a T4)
GEN_N=100                     # held-out statements to evaluate
GEN_K=3                       # samples per problem  -> pass@K
GEN_MAXTOK=1024               # generation length cap (512 truncated 59% of proofs in run 1)
# ----------------------------------------------------------------------------

pip install -q -U transformers trl peft datasets accelerate
python training/scripts/prepare_data.py
python training/scripts/sft_train.py
python training/scripts/gen_preds.py --n "$GEN_N" --k "$GEN_K" --max-new-tokens "$GEN_MAXTOK"
echo "=== run_kaggle.sh done: training/scripts/preds.jsonl written ==="
