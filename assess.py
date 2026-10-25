"""`python -m assess` — pull the latest predictions and write the assessment report.

After a Kaggle run pushes `training/scripts/preds.jsonl` back, run this from the repo root:
it `git pull`s the newest preds, then runs the Lean-verified assessment, writing
`training/output/<ordinal>_training_report-<date>.md` and printing a ready-to-paste README row.

    python -m assess            # pull + assess
    python -m assess --no-pull  # assess whatever preds.jsonl is already local

Any other flags (e.g. `--preds PATH`) are forwarded to the assessment.
"""
import subprocess, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent
ASSESSMENT = ROOT / "training" / "assessment" / "assessment.py"


def main(argv=None):
    argv = list(sys.argv[1:] if argv is None else argv)
    if "--no-pull" in argv:
        argv.remove("--no-pull")
    else:
        print("→ git pull (fetching the latest preds.jsonl) …", flush=True)
        subprocess.run(["git", "pull", "--no-edit", "origin", "main"], cwd=str(ROOT))
    print("→ Lean-verified assessment …\n", flush=True)
    return subprocess.run([sys.executable, str(ASSESSMENT), *argv], cwd=str(ROOT)).returncode


if __name__ == "__main__":
    sys.exit(main())
