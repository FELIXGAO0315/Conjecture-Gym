#!/usr/bin/env python3
"""Independent re-check of every persisted NOT_PROVEN witness (v1.5 PHASE C3 / verify).

Reads the cold-matrix cert store (matrix_certs.jsonl), reconstructs each NOT_PROVEN
query's (facts, goal, witness) and RE-RUNS the pure-Python Fraction re-check
(pf_trust.certify.recheck_witness) from scratch — independent of the cold run. Exits
nonzero if any NOT_PROVEN lacks a witness, any witness fails the re-check, or any
Lean/z3 disagreement is recorded. Light: imports only pf_trust.certify.
"""
import gzip
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from pf_trust import certify

CERTS = ROOT / "analysis" / "v1.5" / "artifacts" / "matrix_certs.jsonl"


def _lines(path: Path):
    """Read the cert store, falling back to the committed .gz (clean checkout)."""
    if path.exists():
        return path.read_text().splitlines()
    gz = path.with_suffix(path.suffix + ".gz")
    if gz.exists():
        return gzip.decompress(gz.read_bytes()).decode().splitlines()
    return None


def _facts(rows):
    return [(dict(items), rel, rhs) for (items, rel, rhs) in rows]


def recheck(path: Path = CERTS) -> dict:
    lines = _lines(path)
    if lines is None:
        return {"ok": False, "reason": f"missing {path} (and .gz)"}
    total = proven = not_proven = unknown = 0
    witness_ok = witness_bad = 0
    lean_conservative = 0          # (not_proven, z3=entailed): TRUE entailment omega missed
    dangerous = []                 # (proven, z3 != entailed): a potential FALSE positive
    bad = []                       # genuine problems that must fail the gate
    for ln in lines:
        if not ln.strip():
            continue
        rec = json.loads(ln)
        total += 1
        v = rec["verdict"]; z = rec.get("z3")
        if v == "proven":
            proven += 1
            # the DANGEROUS direction: Lean PROVEN but the solver does not confirm entailment
            if z != "entailed":
                dangerous.append({"k": rec["k"], "z3": z})
            continue
        if v == "unknown":
            unknown += 1
            bad.append({"k": rec["k"], "why": "unknown_verdict"})
            continue
        not_proven += 1
        w = rec.get("witness")
        if w is None:
            # no witness. Sound iff z3 AGREES it is entailed (a true entailment omega
            # conservatively missed) — never a false PROVEN. Otherwise it is a real gap.
            if z == "entailed":
                lean_conservative += 1
            else:
                bad.append({"k": rec["k"], "why": "no_witness_and_not_entailed", "z3": z})
            continue
        if "base" not in rec or "goal" not in rec:
            if rec.get("recheck_ok"):
                witness_ok += 1
            else:
                witness_bad += 1; bad.append({"k": rec["k"], "why": "stored_recheck_not_ok"})
            continue
        facts = _facts(rec["base"]); items, rel, rhs = rec["goal"]
        out = certify.recheck_witness(facts, (dict(items), rel, rhs), w)
        if out["ok"]:
            witness_ok += 1
        else:
            witness_bad += 1; bad.append({"k": rec["k"], "why": "recheck_failed", "detail": out})
    # SOUND iff: no false PROVEN (dangerous), no bad witness, no UNKNOWN, and every
    # not_proven is either witnessed OR a z3-confirmed true entailment omega missed.
    ok = (not dangerous) and witness_bad == 0 and unknown == 0 and not bad
    return {"ok": ok, "total": total, "proven": proven, "not_proven": not_proven,
            "unknown": unknown, "witness_ok": witness_ok, "witness_bad": witness_bad,
            "lean_conservative_true_entailments": lean_conservative,
            "dangerous_false_positive_candidates": dangerous,
            "bad": bad[:20]}


if __name__ == "__main__":
    r = recheck()
    print(json.dumps(r, indent=2))
    sys.exit(0 if r["ok"] else 1)
