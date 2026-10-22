"""Parametric graph-family generator (PolyForge ⑤) — complete-graph family K_n.

Enumerates relations among the invariants of K_n whose closed forms in n are known
and Mathlib-levered, emits each as a ``∀ n ≥ 1`` Lean theorem proved by a single
validated scaffold (establish (n-1)-regularity + handshake, rewrite invariants to
their closed forms, close with omega / nlinarith), and Lean-verifies every one.

Invariants (closed form on K_n):  ω = n,  maxDeg = minDeg = n-1,  edges = n(n-1)/2.
The relation space is the integer identities among {ω, maxDeg, minDeg} (linear) plus
curated quadratic edge relations.  Unlike the fixed-graph domain these are
parameterized by n (unbounded), a class that domain cannot express.
"""
from __future__ import annotations
import json, hashlib, itertools
from math import gcd
from pathlib import Path
from types import SimpleNamespace

from ...env.verifier import ReplProcess, _REPL_BIN_DEFAULT

_HERE = Path(__file__).resolve().parent
RECORD = _HERE / "record"
_MATHLIB_LEAN = _HERE.parent.parent / "lean"            # shared v4.34 workspace

# ── K_n invariant catalog: lean term + closed form f(n) ───────────────────────
G = "(⊤ : SimpleGraph (Fin n))"
LIN = {                                                  # linear (ℕ) invariants
    "card":   ("(Fintype.card (Fin n))", lambda n: n),
    "omega":  (f"{G}.cliqueNum",   lambda n: n),
    "maxdeg": (f"{G}.maxDegree",   lambda n: n - 1),
    "mindeg": (f"{G}.minDegree",   lambda n: n - 1),
}
EDGES = (f"{G}.edgeFinset.card", lambda n: n * (n - 1) // 2)

PREAMBLE = "import Mathlib\nopen SimpleGraph Finset\n"
SCAFFOLD = """theorem {name} (n : ℕ) (hn : 1 ≤ n) : {stmt} := by
  have hne : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hr : (⊤ : SimpleGraph (Fin n)).IsRegularOfDegree (n - 1) := by
    have h0 := IsRegularOfDegree.top (V := Fin n); rwa [Fintype.card_fin] at h0
  have hd : ∀ v, (⊤ : SimpleGraph (Fin n)).degree v = n - 1 := hr
  have hsum := (⊤ : SimpleGraph (Fin n)).sum_degrees_eq_twice_card_edges
  simp only [hd, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum
  simp only [cliqueNum_top, hr.maxDegree_eq, hr.minDegree_eq, Nat.card_eq_fintype_card,
             Fintype.card_fin]
  all_goals first
    | omega
    | nlinarith [hsum, Nat.zero_le n]
    | (rw [card_edgeFinset_top_eq_card_choose_two, Fintype.card_fin, Nat.choose_two_right]; omega)
"""


# ── enumerate linear identities among {omega, maxdeg, mindeg} ──────────────────
def _term(coeff, lean):
    return lean if coeff == 1 else f"{coeff} * {lean}"

def _side(terms, const):
    """Build a Lean ℕ expression Σ coeff·term (+ const), all nonneg; '0' if empty."""
    parts = [_term(c, LIN[v][0]) for v, c in terms]
    if const:
        parts.append(str(const))
    return " + ".join(parts) if parts else "0"

def _lin_relations():
    names = list(LIN)
    seen, rels = set(), []
    for cs in itertools.product(range(-2, 3), repeat=len(names)):
        if sum(cs) != 0 or all(c == 0 for c in cs):     # sum-zero ⇒ constant-in-n identity
            continue
        g = gcd(*[abs(c) for c in cs if c]) or 1         # canonicalise (primitive, sign)
        cs = tuple(c // g for c in cs)
        lead = next(c for c in cs if c)
        if lead < 0:
            cs = tuple(-c for c in cs)
        if sum(1 for c in cs if c) < 2 or cs in seen:    # need ≥2 invariants
            continue
        seen.add(cs)
        R = sum(c * LIN[v][1](10) for c, v in zip(cs, names))   # constant value
        assert R == sum(c * LIN[v][1](7) for c, v in zip(cs, names))
        pos = [(v, c) for c, v in zip(cs, names) if c > 0]
        neg = [(v, -c) for c, v in zip(cs, names) if c < 0]
        # Σpos + max(-R,0) = Σneg + max(R,0)   (both sides nonneg ℕ)
        lhs = _side(pos, max(-R, 0)); rhs = _side(neg, max(R, 0))
        rels.append((f"{lhs} = {rhs}", sorted(name for name, _c in [*pos, *neg]), 2))
    return rels

def _edge_relations():
    e = EDGES[0]
    return [
        (f"2 * {e} = {LIN['omega'][0]} * {LIN['maxdeg'][0]}", ["omega", "maxdeg", "edges"], 3),
        (f"2 * {e} = {LIN['omega'][0]} * {LIN['mindeg'][0]}", ["omega", "mindeg", "edges"], 3),
        (f"2 * {e} = {LIN['omega'][0]} * ({LIN['omega'][0]} - 1)", ["omega", "edges"], 2),
    ]

def _ineq_relations():
    """Tight single-invariant bounds  x ≤ y (+k)  (good prover-training material)."""
    rels, names = [], list(LIN)
    for x, y in itertools.permutations(names, 2):
        fx, fy = LIN[x][1], LIN[y][1]
        ks = [k for k in range(4) if all(fx(n) <= fy(n) + k for n in range(1, 41))]
        if not ks:
            continue
        k = ks[0]                                        # minimal (tight) offset
        rhs = LIN[y][0] + (f" + {k}" if k else "")
        rels.append((f"{LIN[x][0]} ≤ {rhs}", sorted({x, y}), 2))
    return rels

def relations():
    return _lin_relations() + _edge_relations() + _ineq_relations()


# ── Lean verification (resident Mathlib REPL) ─────────────────────────────────
def _mk_proc():
    return ReplProcess(SimpleNamespace(lean_dir=_MATHLIB_LEAN, repl_preamble="import Mathlib"),
                       _REPL_BIN_DEFAULT, restart_every=10 ** 9)

def _check(proc, src, timeout=30):
    try:
        r = proc._send({"cmd": src, "env": proc.env0}, timeout=timeout)
    except Exception:
        try: proc.start()
        except Exception: pass
        return None
    if any(m.get("severity") == "error" for m in (r.get("messages") or [])):
        return False
    return not r.get("sorries")


def _interest(invs):
    """Adapted interestingness: these relations are EXACT (sharp=1, tight=1); value is
    carried by breadth (#invariants coupled) + the unbounded/parametric nature."""
    breadth = max(0.0, min(1.0, (len(invs) - 2) / 3.0))
    return round(0.50 * 1.0 + 0.25 * 1.0 + 0.25 * breadth, 3)


def _write(out_dir, rec, thm):
    d = out_dir / rec["id"]; d.mkdir(exist_ok=True)
    (d / f"{rec['id']}.json").write_text(json.dumps(rec, ensure_ascii=False, indent=2))
    (d / f"{rec['id']}.lean").write_text(thm)

def generate(out_dir=None, verbose=True, instance_ns=(4,)):
    out_dir = Path(out_dir) if out_dir else RECORD
    out_dir.mkdir(parents=True, exist_ok=True)
    rels = relations()
    proc = _mk_proc()
    records, ok_n, n_cand = [], 0, 0
    for idx, (stmt, invs, _b) in enumerate(rels):
        name = f"K{idx}"
        body = SCAFFOLD.format(name=name, stmt=stmt)
        cmd = "open SimpleGraph Finset\n\n" + body      # REPL env already has `import Mathlib`
        thm = PREAMBLE + "\n" + body                    # standalone file keeps the import
        ok = _check(proc, cmd); n_cand += 1
        rec = {"id": name, "domain": "family", "family": "complete_graph K_n", "kind": "parametric",
               "conjecture": {"natural_language": f"For every n ≥ 1, the complete graph K_n satisfies  {stmt}",
                              "statement_lean": stmt, "quantifier": "∀ n ≥ 1"},
               "invariants": invs, "verified_lean": bool(ok), "interestingness": _interest(invs),
               "proof_tactic": "regularity+handshake; simp; omega|nlinarith",
               "key": hashlib.sha256(stmt.encode()).hexdigest()[:12], "generator": {"version": "family-0.2"}}
        records.append(rec)
        if ok:
            ok_n += 1; _write(out_dir, rec, thm)
            for N in instance_ns:                        # concrete instances (cite the parametric thm)
                istmt = stmt.replace("Fin n", f"Fin {N}")
                iname = f"{name}_n{N}"
                icmd = ("open SimpleGraph Finset\n\n" + body
                        + f"\ntheorem {iname} : {istmt} := {name} {N} (by norm_num)\n")
                iok = _check(proc, icmd); n_cand += 1
                irec = {"id": iname, "domain": "family", "family": "complete_graph K_n",
                        "kind": "instance", "instance_n": N,
                        "conjecture": {"natural_language": f"The complete graph K_{N} satisfies  {istmt}",
                                       "statement_lean": istmt, "quantifier": f"n = {N}"},
                        "invariants": invs, "verified_lean": bool(iok), "interestingness": _interest(invs),
                        "proof_tactic": "specialize parametric", "instance_of": name,
                        "key": hashlib.sha256(istmt.encode()).hexdigest()[:12], "generator": {"version": "family-0.2"}}
                records.append(irec)
                if iok:
                    ok_n += 1
                    _write(out_dir, irec, PREAMBLE + "\n" + body
                           + f"\ntheorem {iname} : {istmt} := {name} {N} (by norm_num)\n")
        if verbose:
            print(f"  {name}: {'OK ' if ok else 'xx '} {stmt}")
    proc.stop()
    return {"family": "K_n", "candidates": n_cand, "verified": ok_n,
            "all_provable": ok_n == n_cand, "record_dir": str(out_dir)}


if __name__ == "__main__":
    print(json.dumps(generate(), ensure_ascii=False, indent=2))
