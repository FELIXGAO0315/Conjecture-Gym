#!/usr/bin/env python3
"""PolyForge v1.4.2 §F2: stratified, skeleton-grouped train/test re-split.

StratifiedGroupKFold (seed 1337, 5 folds → test ≈ 20%), stratified by difficulty tier,
grouped by skeleton so no skeleton appears in both train and test.  Reports per-tier
counts.  Analysis only — the export is NOT changed this round (see the [DECISION]).

Usage: python -m PolyForge.env.stratified_split <export_dir>
"""
import json, sys
from collections import Counter
from pathlib import Path
from sklearn.model_selection import StratifiedGroupKFold


def main(argv):
    export_dir = Path(argv[0])
    tasks = [json.loads(l) for l in (export_dir / "tasks.jsonl").read_text().splitlines() if l.strip()]
    y = [t["difficulty"] for t in tasks]
    groups = [t["skeleton"] for t in tasks]
    X = list(range(len(tasks)))
    sgkf = StratifiedGroupKFold(n_splits=5, shuffle=True, random_state=1337)
    train_idx, test_idx = next(iter(sgkf.split(X, y, groups)))
    test = set(test_idx)
    # verify no skeleton straddles
    tr_sk = {groups[i] for i in train_idx}
    te_sk = {groups[i] for i in test_idx}
    straddle = tr_sk & te_sk
    per = {}
    for tier in ("easy", "medium", "hard"):
        n = sum(1 for t in tasks if t["difficulty"] == tier)
        ntr = sum(1 for i, t in enumerate(tasks) if t["difficulty"] == tier and i not in test)
        nte = n - ntr
        per[tier] = (ntr, nte)
    ntr = len(tasks) - len(test); nte = len(test)
    print(f"stratified group split (StratifiedGroupKFold, seed 1337, 5 folds → ~20% test)")
    print(f"total {len(tasks)}: train {ntr} / test {nte}  (test ratio {nte/len(tasks):.3f})")
    print(f"skeletons: train {len(tr_sk)} test {len(te_sk)}  straddling (must be 0): {len(straddle)}")
    print(f"{'tier':8s} {'train':>6s} {'test':>6s}")
    for tier in ("easy", "medium", "hard"):
        print(f"{tier:8s} {per[tier][0]:>6d} {per[tier][1]:>6d}")
    assert not straddle, "a skeleton straddles train/test — grouping failed"
    print("OK: no skeleton straddles the split")


if __name__ == "__main__":
    main(sys.argv[1:])
