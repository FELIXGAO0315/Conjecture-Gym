#!/usr/bin/env python3
"""v1.5 PHASE G — one-command verification, two tiers (FAST / FULL).

Each gate prints PASS/FAIL; the process exits nonzero on any failure. A canonical,
timestamp-free result JSON is written and a RESULT_HASH (sha256 over the
decision-relevant content, including the cold-matrix fingerprint) is printed, so two
FULL runs from a clean checkout can be compared for hash identity (DoD item 5).
"""
import hashlib
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
TAG = "v1.4.5-published-code"
TAG_COMMIT = "1ba72d0b3c3d7aedbcd3e5cb9c4a444d9bd694dd"
VERIFYDIR = ROOT / "analysis" / "v1.5" / "verify"
ARTIFACTS = ROOT / "analysis" / "v1.5" / "artifacts"
MATRIX_JSON = ROOT / "analysis" / "v1.5" / "matrix_cold.json"

PUBLISHED = [
    "PolyForge/domains/graph/record",
    "PolyForge/domains/graph/data/graph_pool.json",
    "PolyForge/domains/graph/analysis/v1.4.3/export_ladder",
]


def _run(argv, timeout=1200):
    try:
        p = subprocess.run(argv, cwd=str(ROOT), capture_output=True, text=True, timeout=timeout)
        return p.returncode, (p.stdout + p.stderr)[-4000:]
    except subprocess.TimeoutExpired:
        return 124, f"timeout after {timeout}s"


# ───────────────────────────── gates ────────────────────────────────────────
def gate_pins():
    rc, out = _run([sys.executable, "-m", "pf_trust.pins"])
    return rc == 0, out.strip().splitlines()[-1] if out.strip() else "ok"


def gate_pytest():
    rc, out = _run([sys.executable, "-m", "pytest", "pf_trust/tests", "tests",
                    "-q", "-p", "no:cacheprovider"], timeout=1800)
    last = [l for l in out.splitlines() if "passed" in l or "failed" in l or "error" in l]
    return rc == 0, (last[-1] if last else out.strip()[-200:])


def gate_published_identical():
    bad = []
    for p in PUBLISHED:
        rc, _ = _run(["git", "diff", "--quiet", TAG, "--", p])
        if rc != 0:
            bad.append(p)
    return (not bad), ("byte-identical to tag" if not bad else f"DIFFERS: {bad}")


def gate_tag_unmoved():
    rc, out = _run(["git", "rev-parse", f"{TAG}^{{commit}}"])
    got = out.strip()
    return (got == TAG_COMMIT), f"{got} (want {TAG_COMMIT})"


def gate_matrix_recompute():
    # recompute the matrix FROM THE COLD CACHE (warm: no Lean, deterministic) then verify.
    if not (ARTIFACTS / "omega_cold_cache.jsonl").exists():
        return False, "cold cache missing — run analysis/v1.5/matrix_cold.py first"
    rc, out = _run([sys.executable, "analysis/v1.5/matrix_cold.py"], timeout=3600)
    if rc != 0:
        return False, f"matrix_cold.py rc={rc}: {out[-200:]}"
    return gate_matrix_invariants()


def gate_matrix_invariants():
    if not MATRIX_JSON.exists():
        return False, "matrix_cold.json missing"
    m = json.loads(MATRIX_JSON.read_text())
    ts = m["two_sided"]
    checks = {
        "UNKNOWN==0": m["UNKNOWN"]["count"] == 0,
        "no_disagreements": ts["disagreements"] == 0,
        "every_not_proven_has_witness": ts["not_proven"] == ts["not_proven_with_witness"],
        "every_witness_recheck_ok": ts["not_proven"] == ts["not_proven_witness_recheck_ok"],
        "every_proven_solver_unsat": ts["proven"] == ts["proven_solver_unsat_confirmed"],
        "per_judgment_agrees_v147": m["diff_vs_v147"]["per_judgment_disagree"] == 0,
    }
    bad = [k for k, v in checks.items() if not v]
    return (not bad), ("all invariants hold" if not bad else f"VIOLATED: {bad}")


def gate_witness_recheck():
    rc, out = _run([sys.executable, "analysis/v1.5/recheck_witnesses.py"], timeout=600)
    last = out.strip().splitlines()[-1] if out.strip() else ""
    return rc == 0, "independent witness re-check ok" if rc == 0 else out[-200:]


def gate_oracle_persisted():
    # schema = PolyForge.env.oracle_check output (persisted to analysis/v1.5/oracle.json)
    p = ROOT / "analysis" / "v1.5" / "oracle.json"
    if not p.exists():
        return False, "analysis/v1.5/oracle.json missing (run Phase F oracle_check)"
    o = json.loads(p.read_text())
    ok = bool(o.get("all_green"))
    return ok, (f"oracle {o.get('oracle_reward1')}/{o.get('n_tasks')}, "
                f"anti_cheat={'PASS' if o.get('anti_cheat_pass') else 'FAIL'}, "
                f"recompile {o.get('recompile_ok')}/{o.get('recompile_total')}")


def gate_baselines_persisted():
    # schema = analysis/v1.5/baselines.json produced by Phase F (baseline_ladder + L4 status)
    p = ROOT / "analysis" / "v1.5" / "baselines.json"
    if not p.exists():
        return False, "analysis/v1.5/baselines.json missing (run Phase F baselines)"
    b = json.loads(p.read_text())
    ok = bool(b.get("l0_l3_complete")) and bool(b.get("l4_complete"))
    return ok, (f"L0-L3 counts={b.get('level_counts')} none={b.get('none_count')} "
                f"l4_complete={b.get('l4_complete')}")


FAST_GATES = [("version_pins", gate_pins), ("pytest_all", gate_pytest),
              ("published_byte_identical", gate_published_identical),
              ("tag_unmoved", gate_tag_unmoved)]
FULL_EXTRA = [("matrix_recompute_cold", gate_matrix_recompute),
              ("witness_recheck", gate_witness_recheck),
              ("oracle_anticheat_recompile", gate_oracle_persisted),
              ("baselines", gate_baselines_persisted)]


def _matrix_fingerprint():
    if not MATRIX_JSON.exists():
        return None
    m = json.loads(MATRIX_JSON.read_text())
    sub = {
        "M1": [m["M1"]["count"], sorted(m["M1"]["ids"])],
        "M2": [m["M2"]["asc_basis"], m["M2"]["desc_basis"]],
        "C3": [m["C3"]["entailed"], m["C3"]["total"], sorted(m["C3"]["failures"])],
        "UNKNOWN": m["UNKNOWN"]["count"],
        "two_sided": m["two_sided"],
        "graph_soundness": len(m["graph_soundness_violations"]),
        "monotonicity": len(m["monotonicity_violations"]),
        "per_judgment_disagree": m["diff_vs_v147"]["per_judgment_disagree"],
        "attribution": m["loss_attribution"]["attribution"],
    }
    return hashlib.sha256(json.dumps(sub, sort_keys=True).encode()).hexdigest()


def main(mode):
    mode = mode.upper()
    gates = FAST_GATES + (FULL_EXTRA if mode == "FULL" else [])
    results = []
    all_pass = True
    for name, fn in gates:
        try:
            ok, detail = fn()
        except Exception as e:
            ok, detail = False, f"{type(e).__name__}: {e}"
        all_pass = all_pass and ok
        results.append({"gate": name, "status": "PASS" if ok else "FAIL", "detail": detail})
        print(f"GATE {name:28s} {'PASS' if ok else 'FAIL'}  — {detail}")
    canonical = {"mode": mode,
                 "gates": [{"gate": r["gate"], "status": r["status"]} for r in results],
                 "all_pass": all_pass,
                 "matrix_fingerprint": _matrix_fingerprint() if mode == "FULL" else None}
    VERIFYDIR.mkdir(parents=True, exist_ok=True)
    (VERIFYDIR / f"{mode}.json").write_text(json.dumps(canonical, sort_keys=True, indent=2) + "\n")
    (VERIFYDIR / f"{mode}_detail.json").write_text(json.dumps(results, indent=2) + "\n")
    rhash = hashlib.sha256(json.dumps(canonical, sort_keys=True).encode()).hexdigest()
    (VERIFYDIR / f"{mode}.hash").write_text(rhash + "\n")
    print(f"\n{mode} {'PASS' if all_pass else 'FAIL'}  RESULT_HASH {rhash}")
    return 0 if all_pass else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1] if len(sys.argv) > 1 else "FAST"))
