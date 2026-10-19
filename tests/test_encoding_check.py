"""v1.5 review C' — encoding soundness on the real (atlas) population.

Fast live spot-check (sample of nonempty atlas graphs): recompute invariants
independently and confirm every active inventory fact holds; plus verify the
committed full-run artifact is SOUND (0 mismatch / 0 violation).
"""
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(ROOT / "analysis" / "v1.5"))

import encoding_check as EC
from PolyForge.domains.graph import generator as G


def test_differential_and_per_fact_on_atlas_sample():
    pool = [r for r in json.load(open(G.DATA))["graphs"] if r["n"] >= 1]
    sample = pool[::9][:140]                    # deterministic spread across the atlas
    diff_mismatch = 0
    fact_violations = 0
    for rec in sample:
        inv, g, conn = EC.recompute(rec)
        for name, key in EC.POOL_KEY.items():
            if inv.get(name) is None or rec.get(key) is None:
                continue
            if int(rec[key]) != int(inv[name]):
                diff_mismatch += 1
        props = EC.graph_props(rec, g, conn)
        for f in EC.active_linear_facts(props):
            r = EC.eval_fact(f, inv)
            if r is False:
                fact_violations += 1
    assert diff_mismatch == 0, f"independent invariant recomputation disagrees with the pool ({diff_mismatch})"
    assert fact_violations == 0, f"an encoded inventory fact is violated on a real atlas graph ({fact_violations})"


def test_committed_full_run_is_sound():
    p = ROOT / "analysis" / "v1.5" / "encoding_check.json"
    if not p.exists():
        return
    d = json.loads(p.read_text())
    assert d["differential_invariants"]["n_mismatch"] == 0
    assert d["per_fact_validation"]["n_violations"] == 0
    assert "SOUND" in d["verdict"]
    # mutation testing must demonstrate real detection power (some breaking mutants killed)
    assert d["mutation_testing"]["breaking_killed"] > 0


def test_mutation_detects_a_deliberately_false_fact():
    # inject a fact that is FALSE on real graphs (chi <= 0) and confirm the atlas kills it
    pool = [r for r in json.load(open(G.DATA))["graphs"] if r["n"] >= 1]
    false_fact = {"name": "bogus", "coeffs": {"chi": 1}, "rel": "<=", "rhs": 0}  # chi<=0 is false
    killed = False
    for rec in pool[:50]:
        inv, g, conn = EC.recompute(rec)
        if EC.eval_fact(false_fact, inv) is False:
            killed = True
            break
    assert killed, "a deliberately false fact (chi<=0) must be caught by the atlas check"
