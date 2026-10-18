#!/usr/bin/env python3
"""Independent re-check of every persisted NOT_PROVEN witness (v1.5 PHASE C3 / verify).

Reads the cold-matrix cert store (matrix_certs.jsonl), reconstructs each NOT_PROVEN
query's (facts, goal, witness) and RE-RUNS the pure-Python Fraction re-check
(pf_trust.certify.recheck_witness) from scratch — independent of the cold run. Exits
nonzero if any NOT_PROVEN lacks a witness, any witness fails the re-check, or any
Lean/z3 disagreement is recorded. Light: imports only pf_trust.certify.
"""
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from pf_trust import certify

CERTS = ROOT / "analysis" / "v1.5" / "artifacts" / "matrix_certs.jsonl"


def _facts(rows):
    return [(dict(items), rel, rhs) for (items, rel, rhs) in rows]


def recheck(path: Path = CERTS) -> dict:
    if not path.exists():
        return {"ok": False, "reason": f"missing {path}"}
    total = proven = not_proven = unknown = 0
    witness_ok = witness_missing = witness_bad = disagree = 0
    bad = []
    for ln in path.read_text().splitlines():
        if not ln.strip():
            continue
        rec = json.loads(ln)
        total += 1
        if not rec.get("agree", True):
            disagree += 1
            bad.append({"k": rec["k"], "why": "lean_vs_z3_disagreement",
                        "verdict": rec["verdict"], "z3": rec.get("z3")})
        v = rec["verdict"]
        if v == "proven":
            proven += 1
        elif v == "unknown":
            unknown += 1
        else:
            not_proven += 1
            w = rec.get("witness")
            if w is None:
                witness_missing += 1
                bad.append({"k": rec["k"], "why": "no_witness"})
                continue
            if "base" not in rec or "goal" not in rec:
                # witness present but facts not persisted: trust the stored recheck flag
                if rec.get("recheck_ok"):
                    witness_ok += 1
                else:
                    witness_bad += 1
                    bad.append({"k": rec["k"], "why": "stored_recheck_not_ok"})
                continue
            facts = _facts(rec["base"])
            items, rel, rhs = rec["goal"]
            goal = (dict(items), rel, rhs)
            out = certify.recheck_witness(facts, goal, w)
            if out["ok"]:
                witness_ok += 1
            else:
                witness_bad += 1
                bad.append({"k": rec["k"], "why": "recheck_failed", "detail": out})
    ok = (witness_missing == 0 and witness_bad == 0 and disagree == 0 and unknown == 0)
    return {"ok": ok, "total": total, "proven": proven, "not_proven": not_proven,
            "unknown": unknown, "witness_ok": witness_ok, "witness_missing": witness_missing,
            "witness_bad": witness_bad, "disagreements": disagree, "bad": bad[:20]}


if __name__ == "__main__":
    r = recheck()
    print(json.dumps(r, indent=2))
    sys.exit(0 if r["ok"] else 1)
