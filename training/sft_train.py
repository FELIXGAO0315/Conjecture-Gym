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
import json
from pathlib import Path

import torch
from datasets import load_dataset
from transformers import AutoModelForCausalLM, AutoTokenizer
from peft import LoraConfig
from trl import SFTTrainer, SFTConfig

# ────────────────────────────── CONFIG ──────────────────────────────
MODEL      = "Qwen/Qwen2.5-Coder-1.5B-Instruct"   # ← 0.5B option: "Qwen/Qwen2.5-Coder-0.5B-Instruct"
EPOCHS     = 3
LR         = 2e-4
MAX_SEQ    = 2048
BATCH      = 2            # per-device; lower to 1 if OOM
GRAD_ACCUM = 8           # effective batch = BATCH * GRAD_ACCUM
LORA_R     = 16
# ─────────────────────────────────────────────────────────────────────

HERE = Path(__file__).resolve().parent
OUT = HERE / "out"

def main():
    cuda = torch.cuda.is_available()
    dtype = torch.bfloat16 if (cuda and torch.cuda.is_bf16_supported()) else (torch.float16 if cuda else torch.float32)
    print(f"device: {'cuda:'+torch.cuda.get_device_name(0) if cuda else 'CPU (slow — prefer a GPU profile)'}  dtype={dtype}")

    tok = AutoTokenizer.from_pretrained(MODEL)
    if tok.pad_token is None:
        tok.pad_token = tok.eos_token
    model = AutoModelForCausalLM.from_pretrained(MODEL, torch_dtype=dtype,
                                                 device_map="auto" if cuda else None)

    ds = load_dataset("json", data_files=str(HERE / "data" / "train.jsonl"), split="train")
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
        logging_steps=20, save_strategy="epoch",
        bf16=(dtype == torch.bfloat16), fp16=(dtype == torch.float16),
        gradient_checkpointing=True, warmup_ratio=0.03, lr_scheduler_type="cosine",
        report_to="none", assistant_only_loss=True,   # loss on the proof only, not the prompt
    )
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
