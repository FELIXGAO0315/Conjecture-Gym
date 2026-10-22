"""Magma domain — FORWARD generator (matches PolyForge's derive-from-axioms paradigm).

From an oriented axiom set, enumerate free-magma terms, NORMALIZE each, and emit every
non-trivial consequence `∀ vars, t = nf(t)` as a Lean theorem proved by the DERIVATION
PATH (the normalizer's exact rewrite steps as a `rw [..]` chain; `simp only` fallback).
Every record is Lean-verified (resident Mathlib REPL) → all provable, zero undecided.
Difficulty = derivation length, scored with the shared scoring.hardness weights.

Reuses PolyForge infra: scoring.hardness (difficulty), env.verifier.ReplProcess (the
resident-Lean verifier), the shared vendored Mathlib toolchain (PolyForge/lean), and the
record format (record/<id>/<id>.json + .lean).  It does NOT use anvil's LP engine
(magma is a term-rewriting domain, a different engine type).
"""
from __future__ import annotations
import json, hashlib
from pathlib import Path
from types import SimpleNamespace

from ...engine.scoring import hardness as HARD
from ...env.verifier import ReplProcess, _REPL_BIN_DEFAULT
from . import axioms as AX

_HERE = Path(__file__).resolve().parent
RECORD = _HERE / "record"
_MATHLIB_LEAN = _HERE.parent.parent / "lean"         # shared vendored Mathlib workspace (v4.34)
VN = ["a", "b", "c", "d", "e", "f"]

# ── terms / rewriting / normalization ─────────────────────────────────────────
def enum_terms(max_ops, nvars):
    by = {0: [('v', i) for i in range(nvars)]}
    for o in range(1, max_ops + 1):
        by[o] = [('op', l, r) for ol in range(o) for l in by[ol] for r in by[o - 1 - ol]]
    return [t for o in by for t in by[o]]

def _match(pat, t, b):
    if pat[0] == 'v':
        if pat[1] in b: return b[pat[1]] == t
        b[pat[1]] = t; return True
    return t[0] == 'op' and _match(pat[1], t[1], b) and _match(pat[2], t[2], b)
def _subst(pat, b):
    return b[pat[1]] if pat[0] == 'v' else ('op', _subst(pat[1], b), _subst(pat[2], b))
def _rw1(t, axioms):
    for ai, (L, R, nv, _) in enumerate(axioms):
        b = {}
        if _match(L, t, b): return _subst(R, b), True, ai, [b[j] for j in range(nv)]
    if t[0] == 'op':
        nl, ch, ai, ba = _rw1(t[1], axioms)
        if ch: return ('op', nl, t[2]), True, ai, ba
        nr, ch, ai, ba = _rw1(t[2], axioms)
        if ch: return ('op', t[1], nr), True, ai, ba
    return t, False, None, None
def normalize(t, axioms, cap=60):
    steps = []
    while len(steps) < cap:
        t2, ch, ai, ba = _rw1(t, axioms)
        if not ch: break
        t = t2; steps.append((ai, ba))
    return t, steps

def vars_of(t, acc=None):
    acc = acc if acc is not None else []
    if t[0] == 'v':
        if t[1] not in acc: acc.append(t[1])
    else: vars_of(t[1], acc); vars_of(t[2], acc)
    return acc
def term_mul(t): return VN[t[1]] if t[0] == 'v' else f"({term_mul(t[1])} * {term_mul(t[2])})"
def nops(t): return 0 if t[0] == 'v' else 1 + nops(t[1]) + nops(t[2])
def canon(t):
    order = vars_of(t); m = {o: i for i, o in enumerate(order)}
    def ap(x): return ('v', m[x[1]]) if x[0] == 'v' else ('op', ap(x[1]), ap(x[2]))
    return ap(t)

# ── Lean verification (resident Mathlib REPL) ─────────────────────────────────
def _mk_proc():
    return ReplProcess(SimpleNamespace(lean_dir=_MATHLIB_LEAN, repl_preamble="import Mathlib"),
                       _REPL_BIN_DEFAULT, restart_every=10 ** 9)
def _check(proc, src, timeout=30):
    try: r = proc._send({"cmd": src, "env": proc.env0}, timeout=timeout)
    except Exception:
        try: proc.start()
        except Exception: pass
        return None
    if any(m.get("severity") == "error" for m in (r.get("messages") or [])): return False
    return not r.get("sorries")

def _axiom_hyp(ax, i):
    L, R, nv, _ = ax
    return f"(h{i} : ∀ {' '.join(VN[:nv])} : α, {term_mul(L)} = {term_mul(R)})"

def _theorem(name, axioms, t, nf, deriv):
    fv = sorted(set(vars_of(t) + vars_of(nf)))
    binders = " ".join(VN[v] for v in fv)
    hyps = " ".join(_axiom_hyp(a, i) for i, a in enumerate(axioms))
    names = "[" + ", ".join(f"h{i}" for i in range(len(axioms))) + "]"
    chain = ", ".join(f"h{ai} " + " ".join(f"({term_mul(a)})" for a in args) for ai, args in deriv)
    return (f"theorem {name} {{α : Type*}} [Mul α] {hyps} :\n"
            f"    ∀ {binders} : α, {term_mul(t)} = {term_mul(nf)} := by\n"
            f"  intro {binders}\n  first\n  | rw [{chain}]\n  | simp only {names}"), fv

# ── difficulty via the shared scorer (each rewrite = one inventory step) ──────
def _hardness(deriv, ax_names, t, nf, fv):
    steps = [{"rule": "inventory", "inventory": ax_names[ai], "coeffs": {}} for ai, _ in deriv]
    pd = HARD.proof_difficulty(steps, set(ax_names))
    slen = len(fv) + nops(t) + nops(nf) + 2
    return round(pd / max(slen, 1), 3)

# ── driver ────────────────────────────────────────────────────────────────────
def generate(axiom_names, max_ops=4, nvars=3, out_dir=None, prefix="M"):
    out_dir = Path(out_dir) if out_dir else RECORD
    out_dir.mkdir(parents=True, exist_ok=True)
    axioms = AX.get(axiom_names)
    seen, cons = set(), []
    for t in enum_terms(max_ops, nvars):
        nf, deriv = normalize(t, axioms)
        if not deriv or nf == t: continue
        key = (repr(canon(t)), repr(canon(nf)))
        if key in seen: continue
        seen.add(key); cons.append((t, nf, deriv))
    proc = _mk_proc(); records = []; checks = 0
    for idx, (t, nf, deriv) in enumerate(cons):
        name = f"{prefix}{idx}"
        thm, fv = _theorem(name, axioms, t, nf, deriv)
        ok = _check(proc, thm); checks += 1
        if checks % 150 == 0:
            try: proc.start()
            except Exception: pass
        rec = {"id": name, "domain": "magma", "axioms": axiom_names,
               "conjecture": {"natural_language": f"{term_mul(t)} = {term_mul(nf)}",
                              "lhs": term_mul(t), "rhs": term_mul(nf)},
               "derivation_steps": len(deriv), "verified_lean": bool(ok),
               "hardness": _hardness(deriv, axiom_names, t, nf, fv),
               "key": hashlib.sha256(repr((canon(t), canon(nf))).encode()).hexdigest()[:12],
               "generator": {"version": "magma-1.0"}}
        records.append(rec)
        if ok:
            d = out_dir / name; d.mkdir(exist_ok=True)
            (d / f"{name}.json").write_text(json.dumps(rec, ensure_ascii=False, indent=2))
            (d / f"{name}.lean").write_text("import Mathlib\n\n" + thm + "\n")
    proc.stop()
    ver = [r for r in records if r["verified_lean"]]
    hv = sorted(r["hardness"] for r in ver)
    return {"axioms": axiom_names, "max_ops": max_ops, "consequences": len(cons),
            "verified": len(ver), "all_provable": len(ver) == len(records),
            "hardness_min_med_max": [hv[0], hv[len(hv) // 2], hv[-1]] if hv else [],
            "record_dir": str(out_dir)}


if __name__ == "__main__":
    import sys
    axs = sys.argv[1].split(",") if len(sys.argv) > 1 else ["assoc"]
    mo = int(sys.argv[2]) if len(sys.argv) > 2 else 3
    print(json.dumps(generate(axs, max_ops=mo), ensure_ascii=False, indent=2))
