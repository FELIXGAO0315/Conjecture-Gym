"""LoRA SFT of a nano Lean prover on the graph corpus (portable: GPU or CPU).

Reads training/data/train.jsonl (chat messages), fine-tunes a small instruct model with
LoRA, saves the adapter to training/out/.  Auto-detects CUDA (bf16) and falls back to CPU.

On Posit Workbench (JupyterLab or VS Code session):
    pip install -r training/requirements.txt
    python training/prepare_data.py
    python training/sft_train.py
Then download training/out/ and run the local Lean-verified eval (training/eval_lean.py).

Tune the CONFIG block.  No GPU? set MODEL to the 0.5B and expect it slow on CPU.
"""
import os, sys, subprocess, json
# Colab preinstalls an OLD torchao that recent transformers rejects (ImportError in get_peft_model).
# We don't use torchao (plain LoRA) — remove it BEFORE importing transformers so is_torchao_available()
# is False and the version check is skipped.  No-op (silent) if torchao isn't installed.
subprocess.run([sys.executable, "-m", "pip", "uninstall", "-y", "-q", "torchao"],
               stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)

from pathlib import Path

import torch
from datasets import load_dataset
from transformers import AutoModelForCausalLM, AutoTokenizer
from peft import LoraConfig
from trl import SFTTrainer, SFTConfig

# ───────────────── CONFIG (env-overridable, e.g. for a quick smoke test) ──────────────
MODEL      = os.environ.get("SFT_MODEL", "Qwen/Qwen2.5-Coder-1.5B-Instruct")  # 0.5B: "...Coder-0.5B-Instruct"
EPOCHS     = float(os.environ.get("SFT_EPOCHS", "3"))
MAX_STEPS  = int(os.environ.get("SFT_MAX_STEPS", "-1"))   # >0 overrides EPOCHS (smoke test)
LR         = float(os.environ.get("SFT_LR", "2e-4"))
MAX_SEQ    = int(os.environ.get("SFT_MAX_SEQ", "2048"))
BATCH      = int(os.environ.get("SFT_BATCH", "2"))        # per-device; lower to 1 if OOM
GRAD_ACCUM = int(os.environ.get("SFT_GRAD_ACCUM", "8"))   # effective batch = BATCH * GRAD_ACCUM
LORA_R     = int(os.environ.get("SFT_LORA_R", "16"))
# ─────────────────────────────────────────────────────────────────────

HERE = Path(__file__).resolve().parent
OUT = HERE / "out"

def main():
    cuda = torch.cuda.is_available()
    if cuda:
        # bf16 is only real on Ampere+ (compute capability >= 8.0).  On T4 (7.5) bf16 is emulated
        # and breaks matmul ("gemm input BFloat16 output float") — use fp16 there.
        cap = torch.cuda.get_device_capability()[0]
        dtype = torch.bfloat16 if cap >= 8 else torch.float16
    else:
        dtype = torch.float32
    print(f"device: {'cuda:'+torch.cuda.get_device_name(0) if cuda else 'CPU (slow — prefer a GPU profile)'}  dtype={dtype}")

    tok = AutoTokenizer.from_pretrained(MODEL)
    if tok.pad_token is None:
        tok.pad_token = tok.eos_token
    model = AutoModelForCausalLM.from_pretrained(MODEL, torch_dtype=dtype,
                                                 device_map="auto" if cuda else None)

    ds = load_dataset("json", data_files=str(HERE / "data" / "train.jsonl"), split="train")
    # Pre-render each chat into a single text string with the model's template, and train on that
    # plain-text field.  This sidesteps TRL's messages-mode chat-template validation (which requires
    # `{% generation %}` markers that stock Qwen/SmolLM templates lack).
    def _to_text(ex):
        return {"text": tok.apply_chat_template(ex["messages"], tokenize=False,
                                                add_generation_prompt=False)}
    ds = ds.map(_to_text, remove_columns=ds.column_names)
    print(f"train examples: {len(ds)}")

    peft = LoraConfig(r=LORA_R, lora_alpha=LORA_R * 2, lora_dropout=0.05, bias="none",
                      task_type="CAUSAL_LM",
                      target_modules=["q_proj", "k_proj", "v_proj", "o_proj",
                                      "gate_proj", "up_proj", "down_proj"])

    # Build SFTConfig robustly across TRL versions: keep only the args this version accepts
    # (arg names drift between releases — e.g. max_length vs max_seq_length, warmup_ratio).
    import dataclasses
    desired = dict(
        output_dir=str(OUT), num_train_epochs=EPOCHS, learning_rate=LR,
        per_device_train_batch_size=BATCH, gradient_accumulation_steps=GRAD_ACCUM,
        max_length=MAX_SEQ, max_seq_length=MAX_SEQ,
        logging_steps=max(1, 20 if MAX_STEPS < 0 else 1),
        save_strategy=("no" if MAX_STEPS > 0 else "epoch"),
        bf16=(dtype == torch.bfloat16), fp16=(dtype == torch.float16),
        gradient_checkpointing=True, gradient_checkpointing_kwargs={"use_reentrant": False},
        warmup_ratio=0.03, lr_scheduler_type="cosine",
        report_to="none", dataset_text_field="text",   # train on the pre-rendered text field
    )
    if MAX_STEPS > 0:
        desired["max_steps"] = MAX_STEPS
    valid = {f.name for f in dataclasses.fields(SFTConfig)}
    dropped = sorted(set(desired) - valid)
    if dropped:
        print("  (SFTConfig: this TRL version ignores:", dropped, ")")
    cfg = SFTConfig(**{k: v for k, v in desired.items() if k in valid})
    trainer = SFTTrainer(model=model, args=cfg, train_dataset=ds,
                         processing_class=tok, peft_config=peft)
    trainer.train()
    trainer.save_model(str(OUT))
    tok.save_pretrained(str(OUT))
    print(f"\nadapter saved → {OUT}/   (download this, then run training/eval_lean.py locally)")

if __name__ == "__main__":
    main()
