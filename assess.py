"""`python -m assess` — write the Lean-verified assessment report from local predictions.

Predictions are generated locally by `training/scripts/gen_preds.py` into
`training/scripts/preds.jsonl`.  This runs the Lean-verified assessment over them, writing
`training/output/<ordinal>_training_report-<date>.md` and printing a ready-to-paste README row.

    python -m assess            # assess the local preds.jsonl
    python -m assess --pull     # git pull first (if preds were produced on another machine)

Any other flags (e.g. `--preds PATH`) are forwarded to the assessment.
"""
import subprocess, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent
ASSESSMENT = ROOT / "training" / "assessment" / "assessment.py"


def main(argv=None):
    argv = list(sys.argv[1:] if argv is None else argv)
    if "--pull" in argv:
        argv.remove("--pull")
        print("→ git pull (fetching the latest preds.jsonl) …", flush=True)
        subprocess.run(["git", "pull", "--no-edit", "origin", "main"], cwd=str(ROOT))
    print("→ Lean-verified assessment …\n", flush=True)
    return subprocess.run([sys.executable, str(ASSESSMENT), *argv], cwd=str(ROOT)).returncode


if __name__ == "__main__":
    sys.exit(main())
