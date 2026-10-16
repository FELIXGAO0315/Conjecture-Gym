#!/usr/bin/env python3
"""PolyForge v1.4.3 §E: automation-ladder export.

Alongside the unchanged legacy tertile export (``PolyForge.env.export``), emit a
ladder export where every task carries ``auto_level`` (the lowest baseline level that
proves it; see ``baseline_ladder``), the structural ``depth_type``, ``hardness`` and
the stable content ``key``.  ALL tasks are exported (no "core" subset this round).

The train/test split is a StratifiedGroupKFold (seed 1337, 5 folds -> test ~20%)
STRATIFIED BY auto_level and GROUPED BY skeleton, so no skeleton straddles the split.
Per-level train/test counts are reported, plus the legacy per-tier counts.

Usage: python -m PolyForge.env.export_ladder --ladder ladder.json --out DIR
       [--record DIR] [--seed 1337]
"""
import json, sys
from collections import Counter, defaultdict
from pathlib import Path

sys.path.insert(0, "/home/felix_gao/Conjecture-Gym")
from PolyForge.env import tasks as T
from PolyForge.domains.graph import generator as G

LEVELS = ["L0", "U", "L1", "L2", "L3", "none"]


def _split_stratified(tasks, y, groups, seed, n_splits=5):
    from sklearn.model_selection import StratifiedGroupKFold
    # StratifiedGroupKFold needs each stratum to span >= n_splits groups; merge any
    # too-small stratum into a shared "rare" label FOR SPLITTING ONLY (reported counts
    # still use the true auto_level).
    grp_by_y = defaultdict(set)
    for yi, gi in zip(y, groups):
        grp_by_y[yi].add(gi)
    ymap = {lab: (lab if len(gs) >= n_splits else "_rare") for lab, gs in grp_by_y.items()}
    y2 = [ymap[v] for v in y]
    sgkf = StratifiedGroupKFold(n_splits=n_splits, shuffle=True, random_state=seed)
    _, test_idx = next(iter(sgkf.split(range(len(tasks)), y2, groups)))
    return set(test_idx)


def export_ladder(record_dir, ladder_json, out_dir, seed=1337):
    out_dir = Path(out_dir); out_dir.mkdir(parents=True, exist_ok=True)
    ladder = json.loads(Path(ladder_json).read_text())
    auto = ladder["auto_level"]
    domain = "graph"
    base = T.build_tasks(domain, split_seed=seed)          # legacy difficulty + legacy split
    # map record formula -> content key (records carry `key` after the §B migration)
    recs = {}
    for d in Path(record_dir).iterdir():
        jf = d / f"{d.name}.json"
        if jf.exists():
            r = json.loads(jf.read_text())
            recs[r["conjecture"]["formula"]] = r

    rows = []
    for t in base:
        d = t.to_dict()
        rec = recs.get(d["formula"], {})
        d["auto_level"] = auto.get(d["task_id"], "none")
        d["depth_type"] = G._structure_depth_type(d["proof_stats"])
        d["key"] = rec.get("key") or (G.record_content_key(rec) if rec else None)
        d["legacy_split"] = d["split"]
        rows.append(d)

    groups = [d["skeleton"] for d in rows]
    y = [d["auto_level"] for d in rows]
    test = _split_stratified(rows, y, groups, seed)
    for i, d in enumerate(rows):
        d["split"] = "test" if i in test else "train"

    # verify no skeleton straddles
    tr_sk = {groups[i] for i in range(len(rows)) if i not in test}
    te_sk = {groups[i] for i in range(len(rows)) if i in test}
    straddle = tr_sk & te_sk

    per_level = {}
    for lv in LEVELS:
        ntr = sum(1 for i, d in enumerate(rows) if d["auto_level"] == lv and i not in test)
        nte = sum(1 for i, d in enumerate(rows) if d["auto_level"] == lv and i in test)
        per_level[lv] = {"train": ntr, "test": nte, "total": ntr + nte}
    per_tier = {}
    for tier in ("easy", "medium", "hard"):
        ntr = sum(1 for i, d in enumerate(rows) if d["difficulty"] == tier and i not in test)
        nte = sum(1 for i, d in enumerate(rows) if d["difficulty"] == tier and i in test)
        per_tier[tier] = {"train": ntr, "test": nte, "total": ntr + nte}

    with open(out_dir / "tasks.jsonl", "w") as f:
        for d in rows:
            f.write(json.dumps(d, ensure_ascii=False, sort_keys=True) + "\n")
    meta = {
        "env_version": "1.4.3", "domain": domain, "n_tasks": len(rows),
        "export": "automation_ladder (all tasks; no core subset)",
        "ladder_levels": ["L0", "U", "L1", "L2", "L3"],
        "split": {"rule": "StratifiedGroupKFold stratified by auto_level, grouped by skeleton",
                  "seed": seed, "n_splits": 5,
                  "counts": {"train": len(rows) - len(test), "test": len(test)},
                  "test_ratio": round(len(test) / len(rows), 4),
                  "skeleton_straddling": len(straddle),
                  "per_auto_level": per_level, "per_legacy_tier": per_tier},
        "auto_level_counts": {lv: sum(1 for d in rows if d["auto_level"] == lv) for lv in LEVELS},
    }
    (out_dir / "metadata.json").write_text(json.dumps(meta, indent=2))
    print(json.dumps(meta, indent=2))
    assert not straddle, "a skeleton straddles the split"
    return meta


def _main(argv):
    rec = "/home/felix_gao/Conjecture-Gym/PolyForge/domains/graph/record"
    ladder = argv[argv.index("--ladder") + 1]
    out = argv[argv.index("--out") + 1]
    if "--record" in argv:
        rec = argv[argv.index("--record") + 1]
    seed = int(argv[argv.index("--seed") + 1]) if "--seed" in argv else 1337
    export_ladder(rec, ladder, out, seed)


if __name__ == "__main__":
    _main(sys.argv[1:])
