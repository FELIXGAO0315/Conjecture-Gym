"""`python -m assess` — Lean-verify the local predictions, then update the README.

Predictions are generated locally by `training/scripts/gen_preds.py` into
`training/scripts/preds.jsonl`.  This runs the Lean-verified assessment over them (writing
`training/output/<ordinal>_training_report-<date>.md`), then AUTO-UPDATES README.md:
appends the new row to the "Training report" table and bumps the downstream nano-prover
version to `v0.<run#>`.

    python -m assess               # verify + write report + update README
    python -m assess --no-readme   # verify + report only (leave README untouched)
    python -m assess --pull        # git pull first (if preds were produced on another machine)

Any other flags (e.g. `--preds PATH`) are forwarded to the assessment.
"""
import subprocess, sys, json, re
from pathlib import Path

ROOT = Path(__file__).resolve().parent
ASSESSMENT = ROOT / "training" / "assessment" / "assessment.py"
OUTDIR = ROOT / "training" / "output"
README = ROOT / "README.md"


def _latest_summary():
    """The highest-seq assessment summary JSON (written by assessment.py)."""
    best = None
    for p in OUTDIR.glob("*_summary.json"):
        try:
            d = json.loads(p.read_text())
        except Exception:
            continue
        if best is None or d.get("seq", 0) > best.get("seq", 0):
            best = d
    return best


def update_readme(s):
    """Append the training-report row for summary `s` and bump the downstream version.
    Idempotent: if a row for this run number is already present, do nothing."""
    seq = s["seq"]
    text = README.read_text()
    lines = text.splitlines()

    # 1) append the table row (skip if this run # already has a row)
    if not any(re.match(rf"\|\s*{seq}\s*\|", ln) for ln in lines):
        hdr = next((i for i, ln in enumerate(lines)
                    if ln.startswith("| #") and "date" in ln and "pass@k" in ln), None)
        if hdr is None:
            print("!! README: 'Training report' table not found — row not applied")
        else:
            j = hdr + 2                                  # skip header + separator
            while j < len(lines) and lines[j].lstrip().startswith("|"):
                j += 1                                   # j = first non-row line
            lines.insert(j, s["row"])
            print(f"→ README: appended run #{seq} row to the Training report table")
    else:
        print(f"→ README: run #{seq} row already present — left as is")

    text = "\n".join(lines) + ("\n" if text.endswith("\n") else "")

    # 2) bump the downstream version (header + versioning note)
    ver = f"v0.{seq}"
    text, n1 = re.subn(r"nano-prover \(v0\.\d+\)", f"nano-prover ({ver})", text)
    text, n2 = re.subn(r"It is at \*\*v0\.\d+\*\* \(\d+ training rounds",
                       f"It is at **{ver}** ({seq} training rounds", text)
    if n1 or n2:
        print(f"→ README: downstream version → {ver}")

    README.write_text(text)


def main(argv=None):
    argv = list(sys.argv[1:] if argv is None else argv)
    no_readme = "--no-readme" in argv
    if no_readme:
        argv.remove("--no-readme")
    if "--pull" in argv:
        argv.remove("--pull")
        print("→ git pull (fetching the latest preds.jsonl) …", flush=True)
        subprocess.run(["git", "pull", "--no-edit", "origin", "main"], cwd=str(ROOT))

    print("→ Lean-verified assessment …\n", flush=True)
    rc = subprocess.run([sys.executable, str(ASSESSMENT), *argv], cwd=str(ROOT)).returncode
    if rc != 0:
        return rc

    if not no_readme:
        s = _latest_summary()
        if s:
            print()
            update_readme(s)
        else:
            print("!! no assessment summary found — README not updated")
    return 0


if __name__ == "__main__":
    sys.exit(main())
