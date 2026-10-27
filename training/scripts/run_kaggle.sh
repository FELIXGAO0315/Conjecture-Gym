#!/usr/bin/env bash
# ============================================================================
#  nano-prover run config.  The Kaggle cell calls this TWICE:
#    bash run_kaggle.sh train   → install + prepare + fine-tune  (model → training/model/)
#    bash run_kaggle.sh gen     → generate eval proofs           (→ training/scripts/preds.jsonl)
#  The cell pushes the MODEL right after `train` (before the slow `gen`), so a 12 h
#  timeout during generation can never lose the trained model.  EDIT the CONFIG, then push.
# ============================================================================
set -e

# ----------------------------- CONFIG (run 3 — trimmed to fit 12 h with margin) ----
export SFT_MODEL='Qwen/Qwen2.5-Coder-3B-Instruct'   # quick/safe fallback: '...Qwen2.5-Coder-1.5B-Instruct'
export SFT_EPOCHS=1          # 3B is heavy on a T4 — 1 epoch keeps training ~3 h
export SFT_GRAD_CKPT=1
export SFT_BATCH=1
export SFT_GRAD_ACCUM=16    # effective batch 16
export SFT_MAX_SEQ=1024     # 1024 (not 1536) — faster training, most proofs fit
export SFT_LORA_R=32        # bigger adapter than run 2 (was 16)
GEN_N=100
GEN_K=2                     # k=2 (generation on 3B is slow — k=5 is what blew past 12 h last time)
GEN_MAXTOK=1024
GEN_LIMIT=20                # resumable: generate this many NEW per `gen` call, then the cell pushes
# -----------------------------------------------------------------------------------

case "${1:-}" in
  train)
    pip install -q -U transformers trl peft datasets accelerate
    python training/scripts/prepare_data.py
    python training/scripts/sft_train.py ;;
  gen)
    python training/scripts/gen_preds.py --n "$GEN_N" --k "$GEN_K" \
      --max-new-tokens "$GEN_MAXTOK" --limit "$GEN_LIMIT" ;;
  *)
    echo "usage: bash training/scripts/run_kaggle.sh train|gen" ; exit 1 ;;
esac
