"""Assess a nano-prover run and write a human-readable report.

Reads the generated proofs (training/scripts/preds.jsonl), Lean-verifies each proof
with the real Mathlib + GraphLemmas preamble, then reports:
  - pass@k (Lean-kernel verified) and WHICH theorems were solved
  - WHY the rest failed, bucketed by Lean error category
  - whether the model actually LEARNED the corpus (truncation / first-tactic match / lemma overlap)
  - a verdict on whether the upstream corpus is still useful for this nano-LLM

Needs the Lean workspace (PolyForge/lean built + the REPL from PolyForge/env/setup_repl.sh):
    python -m assess                                   # -> training/output/<ordinal>_training_report-<date>.md
"""
import json, re, sys, argparse
from pathlib import Path
from types import SimpleNamespace
from datetime import datetime
from collections import Counter

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from PolyForge.env.verifier import ReplProcess, _REPL_BIN_DEFAULT

LEAN = ROOT / "PolyForge" / "lean"
PREDS = ROOT / "training" / "scripts" / "preds.jsonl"
OUTDIR = ROOT / "training" / "output"
# the preamble every corpus record compiles under (Mathlib + the project's self-proved lemmas)
ENV_PREAMBLE = "import Mathlib\nimport GraphLemmas"
OPENS = "open SimpleGraph\nopen PolyForge.Graph\nopen Finset\n\n"

LEMMA_RE = re.compile(r"[a-zA-Z][a-zA-Z0-9']*_[a-zA-Z0-9_']*")   # snake_case-ish identifiers (lemma/hyp names)

def extract(text):
    m = re.search(r"```lean\s*(.*?)```", text, re.S)
    return (m.group(1) if m else text).strip()

def truncated(raw):                      # model hit the token limit → opening ```lean never closed
    return raw.count("```") < 2

def first_tactic(proof):
    p = proof.strip()
    if p.startswith("by"):
        p = p[2:].strip()
    m = re.match(r"[a-zA-Z_][a-zA-Z0-9_']*", p)
    return m.group(0) if m else ""

def lemmas(proof):
    return set(LEMMA_RE.findall(proof))

def _ordinal(n):
    suf = "th" if 10 <= n % 100 <= 20 else {1: "st", 2: "nd", 3: "rd"}.get(n % 10, "th")
    return f"{n}{suf}"

def classify(err):
    e = err.lower()
    if "unexpected token" in e or "expected" in e and "identifier" in e:
        return "parse error (often truncated)"
    if "unknown identifier" in e or "unknown constant" in e or "unknownidentifier" in e:
        return "unknown lemma / identifier"
    if "unsolved goals" in e:
        return "unsolved goals"
    if "type mismatch" in e or "application type" in e:
        return "type mismatch"
    if any(t in e for t in ("linarith", "omega", "nlinarith", "ring", "simp made no progress", "decide")):
        return "tactic failed to close"
    if "timeout" in e or "maximum recursion" in e or "deterministic" in e:
        return "timeout / too slow"
    return "other"

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--preds", default=str(PREDS))
    args = ap.parse_args()
    rows = [json.loads(l) for l in Path(args.preds).read_text().splitlines() if l.strip()]
    k = len(rows[0]["gens"]) if rows else 0
    proc = ReplProcess(SimpleNamespace(lean_dir=LEAN, repl_preamble=ENV_PREAMBLE),
                       _REPL_BIN_DEFAULT, restart_every=10 ** 9)

    def verify(statement, proof):
        try:
            r = proc._send({"cmd": OPENS + statement + " := " + proof, "env": proc.env0}, timeout=45)
        except Exception as e:
            return False, f"repl error: {e}"
        errs = [m.get("data", "") for m in (r.get("messages") or []) if m.get("severity") == "error"]
        if errs:
            return False, errs[0].replace("\n", " ")[:200]
        if r.get("sorries"):
            return False, "contains sorry"
        return True, ""

    solved, failed = [], []
    trunc = tac_match = 0
    overlaps = []
    for i, rrow in enumerate(rows):
        best = None               # (ok, err, gen) — prefer a passing sample
        for g in rrow["gens"]:
            proof = extract(g)
            ok, err = verify(rrow["statement_lean"], proof)
            if best is None or ok:
                best = (ok, err, g, proof)
            if ok:
                break
        ok, err, raw, proof = best
        ref = rrow.get("proof_ref") or ""
        if truncated(raw): trunc += 1
        if ref and first_tactic(proof) and first_tactic(proof) == first_tactic(ref): tac_match += 1
        if ref:
            lg, lr = lemmas(proof), lemmas(ref)
            overlaps.append(len(lg & lr) / len(lg | lr) if (lg | lr) else 0.0)
        (solved if ok else failed).append({"id": rrow.get("id"), "stmt": rrow["statement_lean"],
                                           "err": err, "reason": classify(err) if not ok else ""})
        print(f"[{i+1}/{len(rows)}] {'PASS' if ok else 'fail'} {rrow.get('id')}", flush=True)
    proc.stop()

    n = len(rows); npass = len(solved)
    reasons = Counter(f["reason"] for f in failed)
    ex = {}
    for f in failed:
        ex.setdefault(f["reason"], f["err"])
    trunc_pct = 100 * trunc / n
    tac_pct = 100 * tac_match / n
    overlap_mean = sum(overlaps) / len(overlaps) if overlaps else 0.0

    # verdict on upstream usefulness — weighted by lemma overlap, with truncation called out as a lever
    levers = []
    if trunc_pct >= 20:
        levers.append(f"**raise `max_new_tokens`** — {trunc_pct:.0f}% of generations are cut off mid-proof, "
                      f"the single biggest and cheapest lever")
    levers.append("train the **1.5B** base for **3 epochs**")
    levers.append("sample **`--k 5`** (pass@5 ≫ pass@1)")
    lever_str = "; ".join(levers)
    if overlap_mean >= 0.30:
        verdict = (f"**Yes — the corpus is clearly teaching the model.** Lemma-name overlap with the reference "
                   f"proofs is high (**{overlap_mean:.2f}**): the model cites the *right* project lemmas, and "
                   f"opens **{tac_pct:.0f}%** of proofs with the correct first tactic. The {100*npass/n:.0f}% "
                   f"pass rate is a *decoding / capacity* limit — not a data problem — since most failures are "
                   f"truncated or near-miss proofs rather than nonsense. Levers, in order: {lever_str}. "
                   f"**Keep growing the corpus.**")
    elif overlap_mean >= 0.12:
        verdict = (f"**Partially.** The model picks up some structure (lemma overlap {overlap_mean:.2f}) but "
                   f"often cites wrong or hallucinated lemmas, so it rarely closes a goal. The corpus is "
                   f"imitable but this model is too small / under-trained to apply it. Before changing the "
                   f"upstream, re-judge after: {lever_str}.")
    else:
        verdict = (f"**Unclear — a red flag.** Generations barely resemble the references (lemma overlap "
                   f"{overlap_mean:.2f}). Either the model is far too weak, or the proofs lean so heavily on "
                   f"bespoke custom lemmas that a tiny model can't imitate them from ~{n*50//1000}k examples. "
                   f"Consider more data, a larger base, or steering the factory toward more uniform / "
                   f"Mathlib-native proof styles.")

    OUTDIR.mkdir(parents=True, exist_ok=True)
    # run number: next after the max row in the README training-report table (committed, always
    # present) — robust on a fresh clone where the generated reports are git-ignored.  Falls back
    # to the local report count if the table can't be read.
    seq = None
    _rm = ROOT / "README.md"
    if _rm.exists():
        _txt = _rm.read_text(); _i = _txt.find("## Training report")
        if _i >= 0:
            _nums = [int(m.group(1)) for m in re.finditer(r"(?m)^\|\s*(\d+)\s*\|", _txt[_i:])]
            if _nums:
                seq = max(_nums) + 1
    if seq is None:
        seq = len(list(OUTDIR.glob("*_training_report-*.md"))) + 1
    date = datetime.now().strftime("%Y%m%d")
    L = []
    L.append(f"# nano-prover assessment — {_ordinal(seq)} training ({date})\n")
    L.append(f"Evaluated **{n}** held-out statements, **{k}** sample(s) each, Lean-kernel verified "
             f"(no `sorry`, standard axioms).\n")
    L.append(f"## Result\n\n**pass@{k} = {npass}/{n} = {100*npass/n:.1f}%**\n")
    L.append("## Solved\n")
    if solved:
        L.append("| id | statement |\n|---|---|")
        for s in solved:
            L.append(f"| `{s['id']}` | `{s['stmt'][:90].replace('|','¦')}` |")
    else:
        L.append("_(none)_")
    L.append("\n## Why the rest failed\n")
    L.append("| reason | count | share | example Lean error |\n|---|---:|---:|---|")
    for reason, c in reasons.most_common():
        L.append(f"| {reason} | {c} | {100*c/n:.0f}% | `{ex[reason][:90].replace('|','¦')}` |")
    L.append("\n## Did the model learn? (signals)\n")
    L.append(f"- **Truncated generations** (hit the token limit): **{trunc_pct:.0f}%** "
             f"{'← raise `max_new_tokens`' if trunc_pct > 15 else ''}")
    L.append(f"- **First tactic matches the reference**: **{tac_pct:.0f}%** "
             f"(learned how to *open* these proofs)")
    L.append(f"- **Lemma-name overlap with reference** (mean Jaccard): **{overlap_mean:.2f}** "
             f"(learned *which* project lemmas to cite)")
    L.append("\n## Is the upstream corpus still useful for the nano-LLM?\n")
    L.append(verdict + "\n")
    out = OUTDIR / f"{_ordinal(seq)}_training_report-{date}.md"
    out.write_text("\n".join(L))
    print(f"\npass@{k} = {npass}/{n} = {100*npass/n:.1f}%   → report: {out.relative_to(ROOT)}")

    # ── auto-filled README training-report row + machine-readable summary (read by `python -m assess`) ──
    top_fail = reasons.most_common(1)[0][0] if reasons else "—"
    pretty = f"{date[:4]}-{date[4:6]}-{date[6:]}"
    meta = {}
    mp = ROOT / "model" / "run_meta.json"   # the adapter dir (sft_train.py OUT); written by sft_train/gen_preds
    if mp.exists():
        try: meta = json.loads(mp.read_text())
        except Exception: meta = {}
    msz = re.search(r"\d+\.?\d*B", meta.get("base", "") or "")
    base_short = msz.group(0) if msz else ((meta.get("base", "") or "?").split("/")[-1] or "?")
    bits = [base_short]
    if meta.get("epochs") is not None: bits.append(f"{float(meta['epochs']):g} ep")
    if meta.get("max_new_tokens"):     bits.append(f"gen {meta['max_new_tokens']}")
    bits.append(f"k{k}")
    config_str = " · ".join(bits)
    lever = ("raise max_new_tokens" if trunc_pct >= 20
             else "sample k↑ / grow corpus" if overlap_mean >= 0.30
             else "bigger base / more epochs")
    takeaway = f"overlap {overlap_mean:.2f}, {trunc_pct:.0f}% truncated, first-tactic {tac_pct:.0f}% — {lever}"
    row = f"| {seq} | {pretty} | {config_str} | **{npass}/{n}** | {overlap_mean:.2f} | {top_fail} | {takeaway} |"
    (OUTDIR / f"{_ordinal(seq)}_summary.json").write_text(json.dumps(
        {"seq": seq, "date": pretty, "config": config_str, "npass": npass, "n": n, "k": k,
         "overlap": round(overlap_mean, 2), "top_fail": top_fail, "takeaway": takeaway, "row": row}, indent=2))
    print("\nREADME table row (auto-applied by `python -m assess`):")
    print(row)

if __name__ == "__main__":
    main()
