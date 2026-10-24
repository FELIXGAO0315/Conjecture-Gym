"""Lean-verify the proofs generated on Colab — run LOCALLY (the Mathlib REPL lives here).

Reads training/preds.jsonl (from gen_preds.py), compiles each generated proof through the
resident Mathlib REPL, and reports real pass@k: a statement is solved iff ANY of its k
generated proofs compiles (no `sorry`, standard axioms).

    python training/verify_preds.py
"""
import json, re, sys
from pathlib import Path
from types import SimpleNamespace

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
HERE = Path(__file__).resolve().parent
from PolyForge.env.verifier import ReplProcess, _REPL_BIN_DEFAULT
LEAN = ROOT / "PolyForge" / "lean"

def extract(text):
    m = re.search(r"```lean\s*(.*?)```", text, re.S)
    return (m.group(1) if m else text).strip()

def main():
    preds = [json.loads(l) for l in (HERE / "preds.jsonl").read_text().splitlines() if l.strip()]
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

    solved = 0
    for i, p in enumerate(preds):
        ok = any(verifies(p["statement_lean"], extract(g)) for g in p["gens"])
        solved += ok
        print(f"[{i+1}/{len(preds)}] {'PASS' if ok else 'fail'}  {p.get('id','')}  {p['statement_lean'][:60]}")
    proc.stop()
    k = len(preds[0]["gens"]) if preds else 0
    print(f"\npass@{k} = {solved}/{len(preds)} = {100*solved/max(1,len(preds)):.1f}%")

if __name__ == "__main__":
    main()
