#!/usr/bin/env python3
"""v1.5 PHASE E — performance of the hardened omega stack (run with Lean idle).

Builds REAL omega queries from the 319 records (inventory-entailment of each record's
conclusion + a sample of per-premise usability checks) — a realistic ~90%-false mix —
and measures ms/target at batch sizes 50/100/200/400/800, >=3 real batches each.
Persists analysis/v1.5/perf.json and recommends max_batch from the throughput.
Replaces stale 11.8 ms citations.
"""
import json
import sys
import time
from pathlib import Path

ROOT = Path("/home/felix_gao/Conjecture-Gym")
sys.path.insert(0, str(ROOT))
from PolyForge.domains.graph.domain import GraphDomain
from PolyForge.anvil import deducer as D
from PolyForge.domains.graph import generator as G
from PolyForge.env import closure_complete as CC
from pf_trust import pins

pins.assert_pins()
dom = GraphDomain(); D.configure(dom)
OUT = ROOT / "analysis" / "v1.5" / "perf.json"
SIZES = [50, 100, 200, 400, 800]
BATCHES_PER_SIZE = 3


def base_of(props, numeric):
    params = {p["name"]: p.get("param") for p in props if "param" in p}
    pset, inv, conds = CC.active_restricted_facts(props, params)
    return [CC._ptuple(pr) for pr in numeric] + inv


def build_pool():
    """Real queries: each record's inventory-entailment (goal = its conclusion) plus a
    sample of per-premise usability checks. Returns [(name, facts, goal, vars)]."""
    final = G.load_records(G.RECORD)
    views = [G._record_premise_view(d) for d in final]
    pool = []
    for T in views:
        base = base_of(T["props"], T["numeric"])
        c = T["canon"]
        goal = ({x: int(k) for x, k in c["coeffs"].items() if int(k) != 0}, c["rel"], int(c["rhs"]))
        vs = sorted({v for f in base for v in f[0]} | set(goal[0]))
        pool.append((f"INV|{T['id']}", base, goal, vs))
    # usability per-premise checks for a stride of record pairs (adds realistic false mix)
    for i, T in enumerate(views):
        base = base_of(T["props"], T["numeric"])
        tv = sorted({v for f in base for v in f[0]})
        R = views[(i + 7) % len(views)]
        for j, pr in enumerate(R["numeric"]):
            g = CC._ptuple(pr)
            pool.append((f"U|{T['id']}|{R['id']}|{j}", base, g, sorted(set(tv) | set(g[0]))))
    return pool


def main():
    pool = build_pool()
    # measure the false fraction on a prefix (one batch) to report the mix
    probe = pool[:400]
    dec, _, _ = CC.omega_decide_batch(probe)
    false_frac = round(1 - sum(1 for v in dec.values() if v) / max(1, len(probe)), 3)
    results = {"false_fraction_probe": false_frac, "pool_size": len(pool), "by_size": {}}
    idx = 0
    for size in SIZES:
        runs = []
        for b in range(BATCHES_PER_SIZE):
            batch = pool[idx: idx + size]
            if len(batch) < size:                       # wrap around the pool if needed
                batch = (batch + pool)[:size]
                idx = size - len(batch)
            idx += size
            t0 = time.time()
            CC.omega_decide_batch(batch)
            dt = time.time() - t0
            runs.append({"n": len(batch), "wall_s": round(dt, 2),
                         "ms_per_target": round(1000 * dt / len(batch), 2)})
        ms = sorted(r["ms_per_target"] for r in runs)
        results["by_size"][str(size)] = {"runs": runs, "median_ms_per_target": ms[len(ms) // 2]}
        print(f"size {size}: median {ms[len(ms)//2]} ms/target "
              f"(runs {[r['ms_per_target'] for r in runs]})", flush=True)
    # recommend max_batch = size with the lowest median ms/target
    best = min(results["by_size"], key=lambda s: results["by_size"][s]["median_ms_per_target"])
    results["recommended_max_batch"] = int(best)
    results["note"] = ("ms/target amortises the per-batch `lake env lean` + Mathlib import "
                       "over the batch; larger batches amortise better until memory. "
                       "Supersedes the stale 11.8 ms citation.")
    OUT.write_text(json.dumps(results, indent=2))
    print("PHASE_E DONE:", json.dumps({"recommended_max_batch": results["recommended_max_batch"],
          "false_fraction": false_frac}), flush=True)


if __name__ == "__main__":
    main()
