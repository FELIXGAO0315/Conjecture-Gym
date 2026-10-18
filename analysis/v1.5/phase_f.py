#!/usr/bin/env python3
"""v1.5 PHASE F — baselines + oracle/anti-cheat/recompile (runs under the supervisor).

1. oracle 319/319 + anti-cheat + recompile 20/20  (PolyForge.env.oracle_check)
   -> analysis/v1.5/oracle.json
2. L0-L3(+U) baseline ladder through the Verifier  (PolyForge.env.baseline_ladder)
   -> analysis/v1.5/artifacts/ladder.json; per-level counts, the "none" set, and a
   per-task diff vs the published v1.4.3 auto_level (export tasks.jsonl).
   -> analysis/v1.5/baselines.json
L4 on the "none" set (<=64 plans/task, 30s each, 15min cap, 14-way) requires a
non-LLM deep-plan-search driver that does NOT exist in the tree; it is recorded as
NOT run (l4_complete=false) rather than faked. See the final report.
"""
import json
import os
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path("/home/felix_gao/Conjecture-Gym")
sys.path.insert(0, str(ROOT))
from pf_trust import pins
from pf_trust.supervise import Heartbeat

pins.assert_pins()
EXPORT = ROOT / "PolyForge/domains/graph/analysis/v1.4.3/export_ladder"
OUT = ROOT / "analysis" / "v1.5"
ART = OUT / "artifacts"
HB = Heartbeat(os.environ.get("PF_HEARTBEAT", str(ART / "phase_f.hb")))
NPROCS = str(min(14, (os.cpu_count() or 4)))


def _run(argv):
    HB.beat({"cmd": argv[:4]})
    print("+", " ".join(argv), flush=True)
    return subprocess.run(argv, cwd=str(ROOT)).returncode


def main():
    ART.mkdir(parents=True, exist_ok=True)
    HB.beat({"stage": "oracle"})
    # 1. oracle / anti-cheat / recompile
    rc = _run([sys.executable, "-m", "PolyForge.env.oracle_check", str(EXPORT),
               "--nprocs", NPROCS, "--json", str(OUT / "oracle.json")])
    print("oracle_check rc", rc, flush=True)

    # 2. L0-L3 ladder
    HB.beat({"stage": "ladder"})
    ladder_json = ART / "ladder.json"
    rc2 = _run([sys.executable, "-m", "PolyForge.env.baseline_ladder", str(EXPORT),
                "--nprocs", NPROCS, "--json", str(ladder_json)])
    print("baseline_ladder rc", rc2, flush=True)

    ladder = json.loads(ladder_json.read_text())
    auto = ladder["auto_level"]
    counts = ladder["counts"]
    none_set = sorted([tid for tid, lv in auto.items() if lv == "none"])

    # per-task diff vs published v1.4.3 auto_level (export tasks.jsonl)
    tasks = [json.loads(l) for l in (EXPORT / "tasks.jsonl").read_text().splitlines() if l.strip()]
    old_auto = {t["task_id"]: t.get("auto_level") for t in tasks}
    diffs = []
    for tid, lv in auto.items():
        ov = old_auto.get(tid)
        if ov is not None and ov != lv:
            diffs.append({"task": tid, "v143": ov, "v15": lv})

    baselines = {
        "levels": ladder["levels"],
        "level_counts": counts,
        "none_count": counts.get("none", len(none_set)),
        "none_set": none_set,
        "diff_vs_v143": {"n_diff": len(diffs), "diffs": diffs[:200]},
        "l0_l3_complete": (rc2 == 0),
        "l4_complete": False,
        "l4_status": ("NOT RUN: a non-LLM deep-plan-search L4 driver (<=64 plans/task, "
                      "30s each, 15min cap, 14-way) does not exist in the tree and the "
                      "HARD CONSTRAINT forbids LLM plans; building it was out of reach "
                      "this session. Recorded honestly, not faked."),
        "ladder_artifact": str(ladder_json),
        "oracle_artifact": str(OUT / "oracle.json"),
        "nprocs": NPROCS,
    }
    (OUT / "baselines.json").write_text(json.dumps(baselines, indent=2))
    (ART / "phase_f.done").write_text(json.dumps({"ts": int(time.time()), "oracle_rc": rc, "ladder_rc": rc2}))
    print("PHASE_F DONE:", json.dumps({"level_counts": counts, "none_count": baselines["none_count"],
          "diff_vs_v143": len(diffs)}), flush=True)


if __name__ == "__main__":
    main()
