#!/usr/bin/env python3
"""PolyForge v1.4.2 §V3: oracle + anti-cheat + standalone recompile over an export.

Oracle: every task's reference_proof must earn reward 1.
Anti-cheat: sorry / admit / set_option / top-level axiom / native_decide / trivial on 8
tasks each must earn reward 0.
Recompile: 20 random record Lean files compile standalone under `lake env lean`.

Usage: python -m PolyForge.env.oracle_check <export_dir> [--record DIR] [--nprocs N] [--json OUT]
Prints a summary and (with --json) writes a machine-readable result.
"""
import json, random, subprocess, sys, time
from pathlib import Path

sys.path.insert(0, "/home/felix_gao/Conjecture-Gym")
from PolyForge.env import verifier as V

ATTACKS = {
    "sorry":        lambda t: "sorry",
    "admit":        lambda t: "admit",
    "set_option":   lambda t: "set_option maxHeartbeats 0 in\n  " + t["reference_proof"],
    "top_axiom":    lambda t: t["reference_proof"] + "\n\naxiom cheat : False",
    "native_decide": lambda t: "native_decide",
    "trivial":      lambda t: "trivial",
}


def main(argv):
    export = Path(argv[0])
    rec = Path("/home/felix_gao/Conjecture-Gym/PolyForge/domains/graph/record")
    lean = Path("/home/felix_gao/Conjecture-Gym/PolyForge/lean")
    nprocs, jout = 4, None
    if "--record" in argv:
        rec = Path(argv[argv.index("--record") + 1])
    if "--nprocs" in argv:
        nprocs = int(argv[argv.index("--nprocs") + 1])
    if "--json" in argv:
        jout = Path(argv[argv.index("--json") + 1])
    # v1.5.1 §D3: the reference proof is no longer in the public task rows; source
    # the full tasks server-side from record/ via build_tasks.
    from PolyForge.env import tasks as T
    tasks = T.full_task_dicts("graph")
    ver = V.Verifier("graph", nprocs=nprocs)
    t0 = time.time()
    ores = ver.verify_batch([(t["task_id"], t["reference_proof"]) for t in tasks])
    oracle_ok = sum(1 for r in ores if r.reward == 1.0)
    oracle_fail = [(r.task_id, r.status) for r in ores if r.reward != 1.0]
    oracle_elapsed = time.time() - t0
    random.seed(1234)
    sample = random.sample(tasks, min(8, len(tasks)))
    anti = {}
    for name, mk in ATTACKS.items():
        ares = ver.verify_batch([(t["task_id"], mk(t)) for t in sample])
        leaks = [(r.task_id, r.reward) for r in ares if r.reward != 0.0]
        anti[name] = {"n": len(ares), "leaks": leaks, "pass": not leaks}
    ver.close()
    random.seed(42)
    dirs = [d for d in rec.iterdir() if d.is_dir() and (d / f"{d.name}.lean").exists()]
    pick = random.sample(dirs, min(20, len(dirs)))
    rc_ok, rc_list = 0, []
    for d in pick:
        src = (d / f"{d.name}.lean").read_text()
        wf = lean / f"{d.name}.lean"; wf.write_text(src)
        r = subprocess.run(["lake", "env", "lean", wf.name], cwd=str(lean), capture_output=True, text=True)
        good = r.returncode == 0 and "error" not in (r.stdout + r.stderr).lower()
        rc_ok += good; rc_list.append((d.name, good)); wf.unlink(missing_ok=True)
    anti_ok = all(v["pass"] for v in anti.values())
    res = {"n_tasks": len(tasks), "oracle_reward1": oracle_ok, "oracle_fail": oracle_fail,
           "oracle_elapsed_s": round(oracle_elapsed, 1), "anti_cheat": anti, "anti_cheat_pass": anti_ok,
           "recompile_ok": rc_ok, "recompile_total": len(pick),
           "all_green": oracle_ok == len(tasks) and anti_ok and rc_ok == len(pick)}
    print(f"ORACLE {oracle_ok}/{len(tasks)} reward1 ({oracle_elapsed:.0f}s); "
          f"ANTI-CHEAT {'PASS' if anti_ok else 'FAIL'}; RECOMPILE {rc_ok}/{len(pick)}; "
          f"{'ALL GREEN' if res['all_green'] else 'ISSUES'}")
    for tid, st in oracle_fail[:10]:
        print("  oracle FAIL", tid, st)
    if jout is not None:
        jout.write_text(json.dumps(res, indent=2)); print("wrote", jout)
    return res


if __name__ == "__main__":
    main(sys.argv[1:])
