#!/usr/bin/env python3
"""PolyForge v1.4.2 §F1: one-line-tactic baseline over the exported graph tasks.

Two levels, each trying tactics {omega, linarith, nlinarith, nlinarith <;> omega}:
  L0 — bare tactic on the task's own hypotheses (premises only);
  L1 — first instantiate every applicable linear Inventory lemma as a `have`
       hypothesis, then the same tactics.
Scoring reuses the oracle's verifier (static scan + compile + env-diff + type match +
standard-axioms), so a "solve" means a genuine reward-1 proof.

Usage: python -m PolyForge.env.baseline <export_dir> [--record <record_dir>] [--nprocs N]
Reports solve counts per difficulty tier and per (structure) depth_type, and the list of
tasks solved at L0.
"""
import json, sys
from collections import defaultdict
from pathlib import Path

sys.path.insert(0, "/home/felix_gao/Conjecture-Gym")
from PolyForge.domains.graph.domain import GraphDomain
from PolyForge.anvil import deducer as D
from PolyForge.domains.graph import generator as G
from PolyForge.domains.graph import formalizer as F
from PolyForge.env import verifier as V

TACTICS = ["omega", "linarith", "nlinarith", "nlinarith <;> omega"]
dom = GraphDomain(); D.configure(dom)


def l1_preamble(data):
    """`have` lines instantiating the applicable linear Inventory lemmas for this task,
    plus the hyp names, reusing the formalizer's wrapper rendering (§F1 L1)."""
    cj = data["conjecture"]
    props = cj["properties_premises"]; numeric = cj["numeric_premises"]
    pset = G.property_closure({p["name"] for p in props})
    params = {p["name"]: p.get("param") for p in props if "param" in p}
    D.configure(dom); G.DED.set_active_inventory(pset, params)
    prop_hyps = {p["name"]: f"hp{i}" for i, p in enumerate(props, 1)}
    lines, names, fid = [], [], 1
    for e in G.DED.INVENTORY:                       # linear Inventory facts only
        if G._has_product(e["conclusion"]["coeffs"]):
            continue
        coeffs, const, rel = D._conc_to_form(e["conclusion"])
        step = {"rule": "inventory", "inventory": e["name"], "fid": fid,
                "coeffs": {v: str(c) for v, c in coeffs.items()}, "const": str(const), "rel": rel}
        buf = []
        try:
            F._emit_step(step, buf, "  ", {}, prop_hyps, {})
        except Exception:
            continue
        lines += buf; names.append(f"s{fid}"); fid += 1
    # identity equalities (Gallai always; tree / regular when premised)
    ids = [("heqg", "gallai_int G")]
    pn = {p["name"] for p in props}
    if "is_tree" in pn:
        ids.append(("heqt", f"tree_edges_int G {prop_hyps['is_tree']}"))
    if "is_regular" in pn:
        hr = prop_hyps["is_regular"]
        ids += [("heqre", f"regular_edges_int G {hr}"), ("heqrx", f"regular_max_int' G {hr}"),
                ("heqrn", f"regular_min_int' G {hr}")]
    for nm, call in ids:
        lines.append(f"  have {nm} := {call}")
        lines.append(f"  try push_cast at {nm}")
        names.append(nm)
    return lines, names


def main(argv):
    export_dir = Path(argv[0])
    rec_dir = Path("/home/felix_gao/Conjecture-Gym/PolyForge/domains/graph/record")
    nprocs = 4
    if "--record" in argv:
        rec_dir = Path(argv[argv.index("--record") + 1])
    if "--nprocs" in argv:
        nprocs = int(argv[argv.index("--nprocs") + 1])
    tasks = [json.loads(l) for l in (export_dir / "tasks.jsonl").read_text().splitlines() if l.strip()]
    recs = {}
    for d in rec_dir.iterdir():
        j = d / f"{d.name}.json"
        if j.exists():
            data = json.load(open(j))
            recs[data["conjecture"]["formula"]] = data
    print(f"{len(tasks)} tasks; {len(recs)} records", flush=True)

    # build L0 and L1 candidate proofs (task, level, tactic_index, proof)
    cand = []
    l1_by_task = {}
    for t in tasks:
        for ti, tac in enumerate(TACTICS):
            cand.append((t["task_id"], "L0", ti, tac))
        data = recs.get(t["formula"])
        if data is not None:
            try:
                lines, names = l1_preamble(data)
                pre = "\n".join(lines)
                refs = "[" + ", ".join(names) + "]" if names else ""
                l1_by_task[t["task_id"]] = True
                for ti, tac in enumerate(TACTICS):
                    body = pre + "\n  " + (tac + " " + refs if refs and tac != "omega" else tac)
                    cand.append((t["task_id"], "L1", ti, body))
            except Exception as ex:
                print("L1 build failed", t["task_id"], ex, flush=True)
    print(f"{len(cand)} candidate (task,level,tactic) proofs to verify", flush=True)

    ver = V.Verifier("graph", nprocs=nprocs)
    import time
    t0 = time.time()
    results = ver.verify_batch([(tid, proof) for tid, _lv, _ti, proof in cand])
    ver.close()
    print(f"verified in {time.time()-t0:.0f}s", flush=True)

    solved = defaultdict(dict)       # task_id -> {"L0": tac_or_None, "L1": tac_or_None}
    for (tid, lv, ti, _proof), r in zip(cand, results):
        if r.reward == 1.0 and solved[tid].get(lv) is None:
            solved[tid][lv] = TACTICS[ti]

    tier = {t["task_id"]: t["difficulty"] for t in tasks}
    sdt = {t["task_id"]: G._structure_depth_type(t["proof_stats"]) for t in tasks}
    tab = defaultdict(lambda: {"n": 0, "L0": 0, "L1": 0})
    tot = {"n": 0, "L0": 0, "L1": 0}
    for t in tasks:
        tid = t["task_id"]; key = (tier[tid], sdt[tid])
        tab[key]["n"] += 1; tot["n"] += 1
        if solved[tid].get("L0"): tab[key]["L0"] += 1; tot["L0"] += 1
        if solved[tid].get("L1"): tab[key]["L1"] += 1; tot["L1"] += 1

    print("\n=== F1 baseline: solved per (tier × structure depth_type) ===")
    print(f"{'tier':8s} {'depth_type':16s} {'n':>4s} {'L0':>5s} {'L1':>5s}")
    for key in sorted(tab):
        c = tab[key]
        print(f"{key[0]:8s} {key[1]:16s} {c['n']:>4d} {c['L0']:>5d} {c['L1']:>5d}")
    print(f"{'TOTAL':8s} {'':16s} {tot['n']:>4d} {tot['L0']:>5d} {tot['L1']:>5d}")
    rate = 100.0 * tot["L0"] / tot["n"]
    print(f"\nL0 solve rate: {tot['L0']}/{tot['n']} = {rate:.1f}%   "
          f"L1 solve rate: {tot['L1']}/{tot['n']} = {100.0*tot['L1']/tot['n']:.1f}%")
    l0list = sorted(tid for tid in solved if solved[tid].get("L0"))
    print(f"\ntasks solved at L0 ({len(l0list)}): " + ", ".join(l0list))
    print(f"\n[DECISION F1] L0 rate {'EXCEEDS' if rate > 30 else 'is below'} 30% "
          f"→ tier recalibration {'PROPOSED (not applied this round)' if rate > 30 else 'not needed'}")


if __name__ == "__main__":
    main(sys.argv[1:])
