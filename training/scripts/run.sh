#!/usr/bin/env bash
# ============================================================================
#  nano-prover run config — local GPU box.
#    bash training/scripts/run.sh train   → install deps + prepare data + LoRA fine-tune
#                                            (adapter → training/model/)
#    bash training/scripts/run.sh gen      → generate eval proofs → training/scripts/preds.jsonl
#    bash training/scripts/run.sh all      → train, then gen
#  Then score locally:  python -m assess
#  Edit the CONFIG block below to change a run.
# ============================================================================
set -e
cd "$(dirname "$0")/../.."          # repo root, regardless of where this is invoked from

# ----------------------------- CONFIG ----------------------------------------------
export SFT_MODEL='Qwen/Qwen2.5-Coder-3B-Instruct'   # scale up freely on a real GPU (7B/14B); 1.5B/0.5B for quick iteration
export SFT_EPOCHS=2
export SFT_GRAD_CKPT=1
export SFT_BATCH=1
export SFT_GRAD_ACCUM=16     # effective batch 16
export SFT_MAX_SEQ=1536      # raise if VRAM allows (most proofs fit in 1024–1536)
export SFT_LORA_R=32
GEN_N=100
GEN_K=5                      # no 12 h wall locally — sample more per statement
GEN_MAXTOK=1280
GEN_LIMIT=0                  # 0 = generate ALL remaining in one pass (resume-safe: skips statements already in preds.jsonl)
# -----------------------------------------------------------------------------------

do_train() {
  python -m pip install -q -U transformers trl peft datasets accelerate
  python training/scripts/prepare_data.py
  python training/scripts/sft_train.py
}
do_gen() {
  python training/scripts/gen_preds.py --n "$GEN_N" --k "$GEN_K" \
    --max-new-tokens "$GEN_MAXTOK" --limit "$GEN_LIMIT"
}

case "${1:-}" in
  train) do_train ;;
  gen)   do_gen ;;
  all)   do_train; do_gen ;;
  *)     echo "usage: bash training/scripts/run.sh train|gen|all" ; exit 1 ;;
esac
