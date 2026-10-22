#!/usr/bin/env python3
"""PolyForge v1.4.2 §F1/§P8: one-line / bounded-tactic baselines over the exported tasks.

Levels (each a "solve" = genuine reward 1 via the oracle verifier path):
  L0  bare tactic on the task's own hypotheses (premises only);
  L1  + all applicable LINEAR Inventory facts as `have`s, then the L0 tactics;
  L2  + the nonlinear/product Inventory facts (handshake, edge-count, card≤α·χ, …) as
      `have`s, then nlinarith variants (nlinarith's degree-2 search multiplies pairs of
      the ≤40 provided facts);
  L3  bounded case split: up to 2 variables whose premise/inventory range has width ≤ 12
      get `interval_cases` (nested), then {omega, nlinarith} with the L2 facts.
Per-task timeout 60 s; tasks verified in parallel; structural depth_type from proof_stats.

Usage: python -m PolyForge.env.baseline <export_dir> [--record DIR] [--nprocs N] [--json OUT]
"""
import json, sys, time
from collections import defaultdict
from pathlib import Path

sys.path.insert(0, "/home/felix_gao/Conjecture-Gym")
from PolyForge.domains.graph.domain import GraphDomain
from PolyForge.anvil import deducer as D
from PolyForge.domains.graph import generator as G
from PolyForge.domains.graph import formalizer as F
from PolyForge.env import verifier as V

TACTICS0 = ["omega", "linarith", "nlinarith", "nlinarith <;> omega"]
TACTICS2 = ["nlinarith {FACTS}", "nlinarith {FACTS} <;> omega", "nlinarith"]
TACTICS3 = ["omega", "nlinarith {FACTS}"]
MAX_HINTS = 40
dom = GraphDomain(); D.configure(dom)
# product-fact Lean wrappers that take only G (no property argument)
_PRODG = {"handshake_min": "handshake_min_int", "handshake_max": "handshake_max_int",
          "edge_card_bound": "two_mul_edges_le_card_sq_sub_card_int",
          "card_le_alpha_chi": "card_le_alpha_chi_int"}
_NAT = {v: z[1:z.rindex(" :")] for v, z in F._Z.items()}   # ℤ term "(X : ℤ)" -> ℕ term "X"


def _active(data):
    cj = data["conjecture"]
    props = cj["properties_premises"]; numeric = cj["numeric_premises"]
    pset = G.property_closure({p["name"] for p in props})
    params = {p["name"]: p.get("param") for p in props if "param" in p}
    G.DED.set_active_inventory(pset, params)
    return props, numeric, pset, params, {p["name"]: f"hp{i}" for i, p in enumerate(props, 1)}


def l1_preamble(data):
    props, numeric, pset, params, prop_hyps = _active(data)
    lines, names, fid = [], [], 1
    for e in G.DED.INVENTORY:
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
    ids = [("heqg", "gallai_int G")]
    pn = {p["name"] for p in props}
    if "is_tree" in pn:
        ids.append(("heqt", f"tree_edges_int G {prop_hyps['is_tree']}"))
    if "is_regular" in pn:
        hr = prop_hyps["is_regular"]
        ids += [("heqre", f"regular_edges_int G {hr}"), ("heqrx", f"regular_max_int' G {hr}"),
                ("heqrn", f"regular_min_int' G {hr}")]
    for nm, call in ids:
        lines.append(f"  have {nm} := {call}"); lines.append(f"  try push_cast at {nm}")
        names.append(nm)
    return lines, names


def l2_preamble(data):
    lines, names = l1_preamble(data)
    props, numeric, pset, params, prop_hyps = _active(data)
    k = 1
    for e in G.DED.PRODUCT_FACTS:
        nm = e["name"]
        if nm in _PRODG:
            call = f"{_PRODG[nm]} G"
        elif nm == "bipartite_edges":
            try:
                call = f"bipartite_four_mul_edges_int G {F._prop_term('is_bipartite', prop_hyps)}"
            except Exception:
                continue
        else:
            continue
        hid = f"p{k}"; lines.append(f"  have {hid} := {call}")
        lines.append(f"  try push_cast at {hid}"); names.append(hid); k += 1
    return lines, names


def _var_bounds(numeric):
    tree = G._build_split_tree(G._premise_forms(numeric), [], D.DEFAULT_SPLIT_DEPTH, products=True)
    out = {}
    for v in G.VARS:
        slo, lo = G._vint(tree, G._cvec({v: 1}), D.DEFAULT_SPLIT_DEPTH)
        shi, neg = G._vint(tree, G._cvec({v: -1}), D.DEFAULT_SPLIT_DEPTH)
        a = lo if slo == "opt" else None
        b = (-neg) if shi == "opt" else None
        if a is not None and b is not None and 0 <= b - a <= 12:
            out[v] = (int(a), int(b))
    return out


def l3_prefix(data):
    """L2 facts + interval_cases on up to 2 small-range variables; returns (lines, names)
    or None if no suitable variable."""
    props, numeric, pset, params, prop_hyps = _active(data)
    usable = G.finite_vars(pset)
    bounds = _var_bounds(numeric)
    pick = [v for v in G.VARS if v in bounds and v in usable and v in _NAT][:2]
    if not pick:
        return None
    lines, names = l2_preamble(data)
    for v in pick:
        b = bounds[v][1]
        lines.append(f"  have hb_{v} : {_NAT[v]} ≤ {b} := by omega")
        lines.append(f"  interval_cases {_NAT[v]}")
    return lines, names


def _mk(level, tac, pre_lines, names):
    facts = "[" + ", ".join(names[:MAX_HINTS]) + "]" if names else "[]"
    body = tac.replace("{FACTS}", facts)
    if level == "L0":
        return body
    return "\n".join(pre_lines) + "\n  " + (body if level != "L3" else f"all_goals ({body})")


def main(argv):
    export_dir = Path(argv[0])
    rec_dir = Path("/home/felix_gao/Conjecture-Gym/PolyForge/domains/graph/record")
    nprocs, jout = 4, None
    if "--record" in argv:
        rec_dir = Path(argv[argv.index("--record") + 1])
    if "--nprocs" in argv:
        nprocs = int(argv[argv.index("--nprocs") + 1])
    if "--json" in argv:
        jout = Path(argv[argv.index("--json") + 1])
    tasks = [json.loads(l) for l in (export_dir / "tasks.jsonl").read_text().splitlines() if l.strip()]
    recs = {}
    for d in rec_dir.iterdir():
        j = d / f"{d.name}.json"
        if j.exists():
            dd = json.load(open(j)); recs[dd["conjecture"]["formula"]] = dd
    print(f"{len(tasks)} tasks; {len(recs)} records", flush=True)

    cand = []
    for t in tasks:
        tid = t["task_id"]; data = recs.get(t["formula"])
        for tac in TACTICS0:
            cand.append((tid, "L0", _mk("L0", tac, None, None)))
        if data is None:
            continue
        try:
            l1l, l1n = l1_preamble(data)
            for tac in TACTICS0:
                cand.append((tid, "L1", _mk("L1", tac, l1l, l1n)))
        except Exception:
            pass
        try:
            l2l, l2n = l2_preamble(data)
            for tac in TACTICS2:
                cand.append((tid, "L2", _mk("L2", tac, l2l, l2n)))
        except Exception:
            pass
        try:
            r = l3_prefix(data)
            if r is not None:
                l3l, l3n = r
                for tac in TACTICS3:
                    cand.append((tid, "L3", _mk("L3", tac, l3l, l3n)))
        except Exception:
            pass
    print(f"{len(cand)} candidate proofs to verify (timeout 60s each)", flush=True)

    ver = V.Verifier("graph", nprocs=nprocs, timeout=60.0)
    t0 = time.time()
    results = ver.verify_batch([(tid, proof) for tid, _lv, proof in cand])
    ver.close()
    print(f"verified in {time.time()-t0:.0f}s", flush=True)

    solved = defaultdict(dict)
    for (tid, lv, _p), r in zip(cand, results):
        if r.reward == 1.0 and solved[tid].get(lv) is None:
            solved[tid][lv] = True

    tier = {t["task_id"]: t["difficulty"] for t in tasks}
    sdt = {t["task_id"]: G._structure_depth_type(t["proof_stats"]) for t in tasks}
    LV = ["L0", "L1", "L2", "L3"]
    tab = defaultdict(lambda: {k: 0 for k in ["n"] + LV})
    tot = {k: 0 for k in ["n"] + LV}
    for t in tasks:
        tid = t["task_id"]; key = (tier[tid], sdt[tid])
        tab[key]["n"] += 1; tot["n"] += 1
        for lv in LV:
            if solved[tid].get(lv):
                tab[key][lv] += 1; tot[lv] += 1

    print("\n=== baseline: solved per (tier × structure depth_type) ===")
    print(f"{'tier':8s} {'depth_type':16s} {'n':>4s} " + " ".join(f"{lv:>4s}" for lv in LV))
    for key in sorted(tab):
        c = tab[key]
        print(f"{key[0]:8s} {key[1]:16s} {c['n']:>4d} " + " ".join(f"{c[lv]:>4d}" for lv in LV))
    print(f"{'TOTAL':8s} {'':16s} {tot['n']:>4d} " + " ".join(f"{tot[lv]:>4d}" for lv in LV))
    for lv in LV:
        print(f"{lv} solve rate: {tot[lv]}/{tot['n']} = {100.0*tot[lv]/tot['n']:.1f}%")
    for lv in ("L2", "L3"):
        sl = sorted(tid for tid in solved if solved[tid].get(lv))
        print(f"tasks solved at {lv} ({len(sl)}): " + ", ".join(sl))
    # §V4 [DECISION]: L2/L3 solving >30% of product_needed/split_needed hard tasks
    for hard_dt in ("product_needed", "split_needed"):
        n = sum(1 for t in tasks if sdt[t["task_id"]] == hard_dt)
        for lv in ("L2", "L3"):
            s = sum(1 for t in tasks if sdt[t["task_id"]] == hard_dt and solved[t["task_id"]].get(lv))
            if n and 100.0 * s / n > 30:
                print(f"[DECISION] {lv} solves {s}/{n}={100.0*s/n:.0f}% of {hard_dt} (>30%) "
                      f"→ PROPOSE difficulty = lowest solving baseline level (not applied)")
    if jout is not None:
        jout.write_text(json.dumps({
            "levels": LV, "total": tot,
            "by_tier_depth": {f"{k[0]}|{k[1]}": v for k, v in tab.items()},
            "solved_L2": sorted(tid for tid in solved if solved[tid].get("L2")),
            "solved_L3": sorted(tid for tid in solved if solved[tid].get("L3")),
        }, indent=2))
        print(f"wrote {jout}")


if __name__ == "__main__":
    main(sys.argv[1:])
