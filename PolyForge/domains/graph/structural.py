"""Structural graph-conjecture generator (PolyForge B — structural layer).

A *second carrier* alongside the LP engine.  Where the LP engine (deducer.py) produces
**linear inequalities among numeric invariants**, proved by one technique (`linarith`),
this module produces **structural conjectures** — implications / equivalences / transfers
among graph *predicates* (IsTree, Connected, IsAcyclic, CliqueFree, Colorable,
IsBipartite, IsPerfectMatching, IsHamiltonianCycle, …) — proved by a *portfolio* of
NON-linarith techniques (term-mode destructuring, lemma citation, implication chaining,
parameter/graph-order monotonicity, `decide`/`simp` on concrete instances).

Design mirrors the existing system: the LP engine stands on the hand-written GraphLemmas
library; this engine stands on a curated INVENTORY of verified Mathlib structural facts,
and a set of COMPOSERS that derive many new conjectures from that inventory.  Every emitted
theorem is Lean-verified against the shared Mathlib workspace before it is kept.

This is the *engine*, not a hand-catalog: N inventory facts × M composition rules → many
conjectures, each with a machine-assembled proof term that Lean checks.
"""
from __future__ import annotations
import json, hashlib, re
from collections import Counter
from pathlib import Path
from types import SimpleNamespace

from ...env.verifier import ReplProcess, _REPL_BIN_DEFAULT
from ...engine.scoring.hardness import structural_difficulty

_HERE = Path(__file__).resolve().parent
RECORD = _HERE / "record_structural"           # graph/record_structural  → S*
_MATHLIB_LEAN = _HERE.parent.parent / "lean"
PREAMBLE = "import Mathlib\nopen SimpleGraph Finset\n"
OPENS = "open SimpleGraph Finset\n\n"

# Binder shared by every "for all graphs G" structural conjecture.
GBIND = "{V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]"
GBIND_FIN = GBIND + " [Finite V]"

# ── INVENTORY ──────────────────────────────────────────────────────────────────
# Base structural IMPLICATIONS over an arbitrary graph G, as predicate pre→post:
#   proof : (h : G.<pre>) ⊢ G.<post>   (G implicit in the surrounding theorem).
# These CHAIN: pre→mid and mid→post give a derived pre→post conjecture.
IMPLICATIONS = [
    # key                pre            post            proof term (h : G.pre) ⊢ G.post
    ("tree_connected",   "IsTree",      "Connected",     "h.1"),
    ("tree_acyclic",     "IsTree",      "IsAcyclic",     "h.2"),
    ("connected_preconn","Connected",   "Preconnected",  "h.preconnected"),
]

# General implications that don't fit the pre/post predicate shape (different binder or
# non-predicate conclusion).  (key, binder, stmt, proof, paradigm)
GENERAL_IMP = [
    ("tree_nonempty", GBIND, "G.IsTree → Nonempty V", "fun h => h.1.nonempty",
        "implication (cite)"),
    ("perfectMatching_matching",
        "{V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {M : G.Subgraph}",
        "M.IsPerfectMatching → M.IsMatching", "fun h => h.1", "implication (destructure)"),
    ("perfectMatching_even",
        "{V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {M : G.Subgraph}",
        "M.IsPerfectMatching → Even (Fintype.card V)", "fun h => h.even_card",
        "matching → parity"),
    # ── deep theorems cited verbatim: the provable frontier toward Barnette-level ──
    ("tutte_sufficient", GBIND,
        "(∀ u, ¬ G.IsTutteViolator u) → ∃ M : G.Subgraph, M.IsPerfectMatching",
        "fun h => G.tutte.mpr h", "deep theorem (Tutte, cite)"),
    ("tutte_iff", GBIND,
        "(∃ M : G.Subgraph, M.IsPerfectMatching) ↔ ∀ u, ¬ G.IsTutteViolator u",
        "G.tutte", "deep theorem (Tutte, iff)"),
]

# Base EQUIVALENCES (iff), cited from Mathlib.  Each emits THREE conjectures: the iff
# itself, plus the forward (`.mp`) and backward (`.mpr`) implications — one inventory
# fact → three conjectures across three paradigms.  (key, lhs, rhs, proof, binder)
EQUIVALENCES = [
    ("chi_le_two_bipartite", "G.chromaticNumber ≤ 2", "G.IsBipartite",
        "chromaticNumber_le_two_iff_isBipartite", GBIND),
    ("colorable_one_bot", "G.Colorable 1", "G = ⊥", "colorable_one_iff", GBIND),
    ("chi_eq_two", "G.chromaticNumber = 2", "G.IsBipartite ∧ G ≠ ⊥",
        "chromaticNumber_eq_two_iff", GBIND),
    ("cliqueNum_card_top", "G.cliqueNum = Nat.card V", "G = ⊤",
        "cliqueNum_eq_natCard", GBIND_FIN),
    ("acyclic_subsingleton_path", "G.IsAcyclic", "∀ u v, Subsingleton (G.Path u v)",
        "isAcyclic_iff_subsingleton_path", GBIND),
]

# Universal structural facts (no premise): (key, binder, stmt, proof, paradigm)
UNIVERSAL = [
    ("colorable_card", GBIND, "G.Colorable (Fintype.card V)", "colorable_of_fintype G",
        "universal (coloring)"),
]

# Parameter-monotone predicate facts (over a numeric parameter, not graph order).
PARAM_MONO = [
    ("cliqueFree_mono_size",
     "(m n : ℕ) (hmn : m ≤ n) (h : G.CliqueFree m) : G.CliqueFree n", "h.mono hmn",
     "monotone (clique size)"),
    ("colorable_mono_count",
     "(m n : ℕ) (hmn : m ≤ n) (h : G.Colorable m) : G.Colorable n", "h.mono hmn",
     "monotone (color count)"),
]

# ── family × invariant templates ───────────────────────────────────────────────
# Each row is a genuinely DIFFERENT theorem FORM (family + invariant + its closed form +
# proof paradigm).  Instancing over a size range gives training volume per paradigm — the
# value is the distinct forms, the sizes are examples for the prover to learn the technique.
#   key, binder(uses {k}), stmt(uses {k},{km1}), proof(uses {k},{km1}), paradigm, min_k
FAMILY_INV = [
    ("complete_cliqueNum", "", "(⊤ : SimpleGraph (Fin {k})).cliqueNum = {k}",
        "by simp [cliqueNum_top]", "simp (complete χ/ω)", 1),
    ("complete_chromatic", "", "(⊤ : SimpleGraph (Fin {k})).chromaticNumber = {k}",
        "by simp [chromaticNumber_top]", "simp (complete χ/ω)", 1),
    ("complete_colorable", "", "(⊤ : SimpleGraph (Fin {k})).Colorable {k}",
        "⟨⟨id, by simp [Function.onFun]⟩⟩", "coloring (witness)", 1),
    ("complete_edges", "", "(⊤ : SimpleGraph (Fin {k})).edgeFinset.card = {k} * ({k} - 1) / 2",
        "by rw [card_edgeFinset_top_eq_card_choose_two, Fintype.card_fin, Nat.choose_two_right]",
        "rw (binomial edges)", 1),
    ("complete_degree", "(v : Fin {k})", "(⊤ : SimpleGraph (Fin {k})).degree v = {km1}",
        "by simp", "simp (degree)", 1),
    ("complete_connected", "", "(⊤ : SimpleGraph (Fin {k})).Connected",
        "by simp [connected_top_iff] <;> omega", "simp (connected)", 2),
    ("empty_cliqueNum", "", "(⊥ : SimpleGraph (Fin {k})).cliqueNum = 1",
        "cliqueNum_bot (Fin {k})", "term (empty)", 1),
    ("empty_edges", "", "(⊥ : SimpleGraph (Fin {k})).edgeFinset.card = 0",
        "by simp", "simp (empty edges)", 1),
    ("empty_cliqueFree2", "", "(⊥ : SimpleGraph (Fin {k})).CliqueFree 2",
        "cliqueFree_bot (by norm_num)", "term (cliqueFree bot)", 1),
    ("path_connected", "", "(pathGraph {k}).Connected",
        "pathGraph_connected {km1}", "term (path connected)", 1),
    ("path_bipartite", "", "(pathGraph {k}).IsBipartite",
        "IsBipartite.pathGraph {k}", "term (path bipartite)", 1),
    ("path_chromatic", "", "(pathGraph {k}).chromaticNumber = 2",
        "chromaticNumber_pathGraph {k} (by norm_num)", "term-mode (path χ)", 2),
    ("cycle_connected", "", "(cycleGraph {k}).Connected",
        "cycleGraph_connected", "term (cycle connected)", 3),
    ("cycle_edges", "", "(cycleGraph {k}).edgeFinset.card = {k}",
        "by\n  have hsum := (cycleGraph {k}).sum_degrees_eq_twice_card_edges\n"
        "  have hdeg : ∀ v, (cycleGraph {k}).degree v = 2 := fun v => cycleGraph_degree_three_le\n"
        "  simp only [hdeg, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum\n"
        "  omega", "handshake + omega", 3),
    ("cycle_degree", "(v : Fin {k})", "(cycleGraph {k}).degree v = 2",
        "cycleGraph_degree_three_le", "term (cycle regular)", 3),
]
FAMILY_INV_KS = tuple(range(3, 41))        # size range per family-invariant form

# complete-bipartite / star edge counts over (a, b)
BIPARTITE_AB = [(a, b) for a in (1, 2, 3) for b in range(a, 9)]

# cycle / path chromatic via parity, wider range (parity-case paradigm volume)
FAMILY_CHI_KS = tuple(range(4, 41))


def _mk_proc():
    return ReplProcess(SimpleNamespace(lean_dir=_MATHLIB_LEAN, repl_preamble="import Mathlib"),
                       _REPL_BIN_DEFAULT, restart_every=10 ** 9)

def _check(proc, cmd, timeout=40):
    try:
        r = proc._send({"cmd": cmd, "env": proc.env0}, timeout=timeout)
    except Exception:
        try: proc.start()
        except Exception: pass
        return None
    if any(m.get("severity") == "error" for m in (r.get("messages") or [])):
        return False
    return not r.get("sorries")


# ── COMPOSERS: each yields candidate dicts with an explicit `sig` (everything between the
#    theorem name and `:=`) plus `proof`.  `stmt` is the human-facing conclusion for records. ──
def compose_implications():
    """Direct base implications + 2-step chains pre→mid→post."""
    out = []
    for key, pre, post, pf in IMPLICATIONS:
        stmt = f"G.{pre} → G.{post}"
        out.append(dict(name=f"imp_{key}", sig=f"{GBIND} :\n    {stmt}", stmt=stmt,
                        proof=f"fun h => {pf}", paradigm="implication (destructure/cite)",
                        ctype="structural implication", meta={"pre": pre, "post": post}))
    # 2-step chains: (pre→mid) then (mid→post) ⟹ pre→post
    by_pre = {}
    for k, pre, post, pf in IMPLICATIONS:
        by_pre.setdefault(pre, []).append((k, pre, post, pf))
    for k1, pre1, mid, pf1 in IMPLICATIONS:
        for k2, pre2, post2, pf2 in by_pre.get(mid, []):
            if post2 == pre1:
                continue
            stmt = f"G.{pre1} → G.{post2}"
            out.append(dict(name=f"chain_{pre1}_{post2}", sig=f"{GBIND} :\n    {stmt}",
                            stmt=stmt,
                            proof=f"fun h => (fun hm => {pf2}) ((fun h => {pf1}) h)",
                            paradigm="implication chain (∘)",
                            ctype="structural implication",
                            meta={"pre": pre1, "mid": mid, "post": post2}))
    return out

def compose_general_imp():
    out = []
    for key, binder, stmt, pf, par in GENERAL_IMP:
        out.append(dict(name=f"gimp_{key}", sig=f"{binder} :\n    {stmt}", stmt=stmt,
                        proof=pf, paradigm=par, ctype="structural implication", meta={}))
    return out

def compose_equivalences():
    """Each iff → iff conjecture + forward (.mp) + backward (.mpr) implications."""
    out = []
    for key, lhs, rhs, pf, binder in EQUIVALENCES:
        out.append(dict(name=f"iff_{key}", sig=f"{binder} :\n    {lhs} ↔ {rhs}",
                        stmt=f"{lhs} ↔ {rhs}", proof=pf,
                        paradigm="equivalence (iff cite)",
                        ctype="structural equivalence", meta={}))
        out.append(dict(name=f"iffmp_{key}", sig=f"{binder} :\n    {lhs} → {rhs}",
                        stmt=f"{lhs} → {rhs}", proof=f"fun h => ({pf}).mp h",
                        paradigm="implication (iff.mp)",
                        ctype="structural implication", meta={}))
        out.append(dict(name=f"iffmpr_{key}", sig=f"{binder} :\n    {rhs} → {lhs}",
                        stmt=f"{rhs} → {lhs}", proof=f"fun h => ({pf}).mpr h",
                        paradigm="implication (iff.mpr)",
                        ctype="structural implication", meta={}))
    return out

def compose_universal():
    out = []
    for key, binder, stmt, pf, par in UNIVERSAL:
        out.append(dict(name=f"univ_{key}", sig=f"{binder} :\n    {stmt}", stmt=stmt,
                        proof=pf, paradigm=par, ctype="structural universal", meta={}))
    return out

def compose_param_mono():
    out = []
    for key, stmt, pf, par in PARAM_MONO:
        out.append(dict(name=f"pm_{key}", sig=f"{GBIND} {stmt}", stmt=stmt, proof=pf,
                        paradigm=par, ctype="structural monotonicity", meta={}))
    return out

def compose_instances():
    """family × invariant templates, instanced over a size range (training volume per form)."""
    out = []
    for key, binder, tmpl, pf, par, mink in FAMILY_INV:
        for k in FAMILY_INV_KS:
            if k < mink:
                continue
            rep = {"{k}": str(k), "{km1}": str(k - 1)}
            stmt, proof, bnd = tmpl, pf, binder
            for a, b in rep.items():
                stmt = stmt.replace(a, b); proof = proof.replace(a, b); bnd = bnd.replace(a, b)
            bsig = (bnd + " ") if bnd else ""
            out.append(dict(name=f"inst_{key}_{k}", sig=f"{bsig}:\n    {stmt}", stmt=stmt,
                            proof=proof, paradigm=par, ctype="structural instance",
                            meta={"family": key, "k": k}))
    return out

def compose_bipartite():
    out = []
    for a, b in BIPARTITE_AB:
        fam = "star K_{1,n}" if a == 1 else "complete bipartite K_{m,n}"
        stmt = f"(completeBipartiteGraph (Fin {a}) (Fin {b})).edgeSet.encard = {a}*{b}"
        out.append(dict(name=f"cbip_{a}_{b}", sig=f":\n    {stmt}", stmt=stmt,
                        proof="by rw [encard_edgeSet_completeBipartiteGraph]; simp",
                        paradigm="rw (bipartite edges)", ctype="structural instance",
                        meta={"family": fam, "a": a, "b": b}))
    return out

def compose_family_chromatic():
    """cycleGraph parity (even→2, odd→3) over a range of sizes — genuine parity-case reasoning."""
    out = []
    for k in FAMILY_CHI_KS:
        if k % 2 == 0:
            stmt, pf = (f"(cycleGraph {k}).chromaticNumber = 2",
                        f"chromaticNumber_cycleGraph_of_even {k} (by norm_num) (by decide)")
        else:
            stmt, pf = (f"(cycleGraph {k}).chromaticNumber = 3",
                        f"chromaticNumber_cycleGraph_of_odd {k} (by norm_num) (by decide)")
        out.append(dict(name=f"cyc_chi_{k}", sig=f":\n    {stmt}", stmt=stmt, proof=pf,
                        paradigm="parity-case (cycle χ)", ctype="structural instance",
                        meta={"family": "cycle Cₙ", "k": k}))
    return out

COMPOSERS = [compose_implications, compose_general_imp, compose_equivalences,
             compose_universal, compose_param_mono, compose_instances,
             compose_bipartite, compose_family_chromatic]


def _thm(name, c):
    return f"theorem {name} {c['sig']} := {c['proof']}"


def _verify_chunk(args):
    """Worker: own Lean REPL, verify a chunk of (gidx, theorem_text) → [(gidx, ok)]."""
    chunk = args
    proc = _mk_proc()
    out = []
    for gidx, thm in chunk:
        out.append((gidx, bool(_check(proc, OPENS + thm))))
    proc.stop()
    return out


def _chunks(L, n):
    for i in range(0, len(L), n):
        yield L[i:i + n]


def generate(out_dir=None, verbose=True, workers=8):
    out_dir = Path(out_dir) if out_dir else RECORD
    out_dir.mkdir(parents=True, exist_ok=True)
    import shutil, multiprocessing as mp
    for d in out_dir.glob("S*"):
        if d.is_dir(): shutil.rmtree(d, ignore_errors=True)

    cands = []
    for comp in COMPOSERS:
        cands.extend(comp())
    thms = [_thm(f"S{i}", c) for i, c in enumerate(cands)]

    # parallel Lean verification across `workers` REPLs (one-by-one within a worker)
    tasks = list(_chunks(list(enumerate(thms)), max(1, len(thms) // (workers * 4) + 1)))
    oks = {}
    with mp.get_context("fork").Pool(workers) as p:
        for res in p.imap_unordered(_verify_chunk, tasks, chunksize=1):
            for gidx, ok in res:
                oks[gidx] = ok

    records, ok_n = [], 0
    for idx, c in enumerate(cands):
        name = f"S{idx}"; thm = thms[idx]; ok = oks.get(idx, False)
        diff = structural_difficulty(c["paradigm"], c["stmt"], c.get("meta"))
        rec = {"id": name, "domain": "graph-structural", "kind": "structural",
               "conjecture_type": c["ctype"], "paradigm": c["paradigm"],
               "difficulty": diff, "verified_lean": bool(ok),
               "conjecture": {"statement_lean": c["stmt"], "quantifier": "∀G"},
               "proof_lean": c["proof"], "meta": c["meta"],
               "key": hashlib.sha256(thm.encode()).hexdigest()[:12],
               "generator": {"version": "structural-B-0.2"}}
        records.append(rec)
        if ok:
            ok_n += 1
            d = out_dir / name; d.mkdir(exist_ok=True)
            (d / f"{name}.json").write_text(json.dumps(rec, ensure_ascii=False, indent=2))
            (d / f"{name}.lean").write_text(PREAMBLE + "\n" + thm + "\n")

    by_type = Counter(r["conjecture_type"] for r in records if r["verified_lean"])
    by_par = Counter(r["paradigm"] for r in records if r["verified_lean"])
    ds = sorted(r["difficulty"] for r in records if r["verified_lean"])
    diff_stats = ({"min": ds[0], "mean": round(sum(ds) / len(ds), 2), "max": ds[-1]}
                  if ds else {})
    if verbose:
        print(f"structural: {ok_n}/{len(cands)} verified  types={dict(by_type)}")
        print(f"  paradigms={dict(by_par)}")
    return {"candidates": len(cands), "verified": ok_n,
            "conjecture_types": dict(by_type), "paradigms": dict(by_par),
            "difficulty": diff_stats, "record_dir": str(out_dir)}


if __name__ == "__main__":
    print(json.dumps(generate(), ensure_ascii=False, indent=2))
