"""Parametric graph-family generator (PolyForge B2).

Generates ``∀ n`` / ``∀ m,n`` conjectures about graph FAMILIES — a class the fixed-graph
LP engine cannot express — and proves each with a proof style CHOSEN PER (family,
invariant), so the corpus spans genuinely different proof paradigms (parity-case
`rcases`, term-mode citation, `rw`/`simp`, handshake+`omega`, regularity) instead of one
scaffold.  Concrete instances (``theorem t : stmt[n:=N] := parent N``) multiply volume.
Every theorem is Lean-verified against the shared Mathlib workspace.  B2 = new proof
PARADIGMS from the engine itself; it only cites Mathlib's family APIs as lemmas.
"""
from __future__ import annotations
import json, hashlib, re
from collections import Counter
from pathlib import Path
from types import SimpleNamespace

from ...env.verifier import ReplProcess, _REPL_BIN_DEFAULT

_HERE = Path(__file__).resolve().parent
RECORD = _HERE / "record_parametric"      # graph/record_parametric (graph/record is the LP-engine C*)
_MATHLIB_LEAN = _HERE.parent.parent / "lean"

# entry: name, family, paradigm, binder, stmt (type, uses `n`), proof, inst (arg-for-N | None)
def E(name, family, paradigm, binder, stmt, proof, inst=None):
    return dict(name=name, family=family, paradigm=paradigm, binder=binder,
                stmt=stmt, proof=proof, inst=inst)

CATALOG = [
    E("chi_cycle_parity", "cycle Cₙ", "cases/parity (rcases)", "(n : ℕ) (h : 2 ≤ n)",
      "(cycleGraph n).chromaticNumber = if Even n then 2 else 3",
      "by\n  rcases Nat.even_or_odd n with he | ho\n"
      "  · rw [if_pos he, chromaticNumber_cycleGraph_of_even n h he]\n"
      "  · rw [if_neg (by simpa [Nat.not_even_iff_odd] using ho),\n"
      "        chromaticNumber_cycleGraph_of_odd n h ho]",
      inst=lambda N: f"{N} (by norm_num)"),
    E("edges_complete", "complete Kₙ", "rw (binomial)", "(n : ℕ)",
      "(⊤ : SimpleGraph (Fin n)).edgeFinset.card = n * (n - 1) / 2",
      "by rw [card_edgeFinset_top_eq_card_choose_two, Fintype.card_fin, Nat.choose_two_right]",
      inst=lambda N: f"{N}"),
    E("edges_bipartite", "complete bipartite K_{m,n}", "rw (encard)", "(m n : ℕ)",
      "(completeBipartiteGraph (Fin m) (Fin n)).edgeSet.encard = m * n",
      "by rw [encard_edgeSet_completeBipartiteGraph]; simp"),
    E("clique_complete", "complete Kₙ", "simp", "(n : ℕ)",
      "(⊤ : SimpleGraph (Fin n)).cliqueNum = n", "by simp [cliqueNum_top]",
      inst=lambda N: f"{N}"),
    E("chi_complete", "complete Kₙ", "simp", "(n : ℕ)",
      "(⊤ : SimpleGraph (Fin n)).chromaticNumber = n", "by simp [chromaticNumber_top]",
      inst=lambda N: f"{N}"),
    E("cycle_two_regular", "cycle Cₙ", "term-mode", "(n : ℕ) (v : Fin (n + 3))",
      "(cycleGraph (n + 3)).degree v = 2", "cycleGraph_degree_three_le"),
    E("edges_cycle", "cycle Cₙ", "handshake + omega", "(n : ℕ)",
      "(cycleGraph (n + 3)).edgeFinset.card = n + 3",
      "by\n  have hsum := (cycleGraph (n + 3)).sum_degrees_eq_twice_card_edges\n"
      "  have hdeg : ∀ v, (cycleGraph (n + 3)).degree v = 2 := fun v => cycleGraph_degree_three_le\n"
      "  simp only [hdeg, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum\n"
      "  omega", inst=lambda N: f"{N}"),
    E("chi_path", "path Pₙ", "term-mode", "(n : ℕ) (h : 2 ≤ n)",
      "(pathGraph n).chromaticNumber = 2", "chromaticNumber_pathGraph n h",
      inst=lambda N: f"{N} (by norm_num)"),
    E("girth_complete", "complete Kₙ", "term + omega", "(n : ℕ) (h : 3 ≤ n)",
      "(⊤ : SimpleGraph (Fin n)).girth = 3", "girth_top (by simp; omega)",
      inst=lambda N: f"{N} (by norm_num)"),
    E("clique_bot", "empty ⊥ₙ", "term-mode", "(n : ℕ)",
      "(⊥ : SimpleGraph (Fin (n+1))).cliqueNum = 1", "cliqueNum_bot (Fin (n+1))",
      inst=lambda N: f"{N}"),
    E("chi_bot", "empty ⊥ₙ", "term-mode", "(n : ℕ)",
      "(⊥ : SimpleGraph (Fin (n+1))).chromaticNumber = 1", "chromaticNumber_bot",
      inst=lambda N: f"{N}"),
    E("cycle_connected", "cycle Cₙ", "term (property)", "(n : ℕ)",
      "(cycleGraph (n + 1)).Connected", "cycleGraph_connected", inst=lambda N: f"{N}"),
    E("path_connected", "path Pₙ", "term (property)", "(n : ℕ)",
      "(pathGraph (n + 1)).Connected", "pathGraph_connected n", inst=lambda N: f"{N}"),
    E("maxdeg_complete", "complete Kₙ", "regularity + rw", "(n : ℕ)",
      "(⊤ : SimpleGraph (Fin (n+1))).maxDegree = n",
      "by\n  have hr : (⊤ : SimpleGraph (Fin (n+1))).IsRegularOfDegree n := by\n"
      "    have := IsRegularOfDegree.top (V := Fin (n+1)); rwa [Fintype.card_fin] at this\n"
      "  rw [hr.maxDegree_eq]", inst=lambda N: f"{N}"),
    E("chi_mono_path_cycle", "path/cycle", "monotonicity (mono)", "(n : ℕ)",
      "(pathGraph n).chromaticNumber ≤ (cycleGraph n).chromaticNumber",
      "chromaticNumber_mono (cycleGraph n) pathGraph_le_cycleGraph", inst=lambda N: f"{N}"),
    E("cycle_not_acyclic", "cycle Cₙ", "negation (intro+exact)", "(n : ℕ)",
      "¬ (cycleGraph (n + 3)).IsAcyclic",
      "by\n  intro h\n  exact h (cycleGraph.cycle n) cycleGraph.isCycle_cycle", inst=lambda N: f"{N}"),
    E("omega_eq_chi_calc", "complete Kₙ", "calc (chained)", "(n : ℕ)",
      "((⊤ : SimpleGraph (Fin n)).cliqueNum : ℕ∞) = (⊤ : SimpleGraph (Fin n)).chromaticNumber",
      "by\n  calc ((⊤ : SimpleGraph (Fin n)).cliqueNum : ℕ∞) = (n : ℕ∞) := by simp [cliqueNum_top]\n"
      "    _ = (⊤ : SimpleGraph (Fin n)).chromaticNumber := by simp [chromaticNumber_top]",
      inst=lambda N: f"{N}"),
    E("edges_star", "star K_{1,n}", "rw (star)", "(n : ℕ)",
      "(completeBipartiteGraph (Fin 1) (Fin n)).edgeSet.encard = n",
      "by rw [encard_edgeSet_completeBipartiteGraph]; simp", inst=lambda N: f"{N}"),
    E("bipartite_path", "path Pₙ", "term (property)", "(n : ℕ)",
      "(pathGraph n).IsBipartite", "IsBipartite.pathGraph n", inst=lambda N: f"{N}"),
    E("bipartite_cycle_even", "cycle Cₙ", "term (property/parity)", "(n : ℕ) (he : Even n)",
      "(cycleGraph n).IsBipartite", "IsBipartite.cycleGraph_of_even he"),
    E("tau_complete", "complete Kₙ", "rw + simp", "(n : ℕ)",
      "(completeGraph (Fin n)).vertexCoverNum = (n : ℕ∞) - 1",
      "by rw [vertexCoverNum_top]; simp", inst=lambda N: f"{N}"),
    E("turan_cliquefree", "Turán T(n,r)", "term (property)", "(n r : ℕ) (hr : 0 < r)",
      "(turanGraph n r).CliqueFree (r + 1)", "turanGraph_cliqueFree hr"),
    # ── v2.1: new families / invariants / proof paradigms (strategy diversity) ──
    E("cycle_eq_circulant", "circulant Circ{1}", "term (family identity)", "(n : ℕ)",
      "cycleGraph (n + 1) = circulantGraph {1}", "cycleGraph_eq_circulantGraph n"),
    E("compl_bot_fam", "complement ⊥ᶜ", "term (complement)", "(n : ℕ)",
      "(⊥ : SimpleGraph (Fin n))ᶜ = ⊤", "compl_bot"),
    E("compl_top_fam", "complement ⊤ᶜ", "term (complement)", "(n : ℕ)",
      "(⊤ : SimpleGraph (Fin n))ᶜ = ⊥", "compl_top"),
    E("multipartite_top", "complete-multipartite ⊤", "term (property)", "(n : ℕ)",
      "(⊤ : SimpleGraph (Fin n)).IsCompleteMultipartite", "IsCompleteMultipartite.top"),
    E("multipartite_bot", "complete-multipartite ⊥", "term (property)", "(n : ℕ)",
      "(⊥ : SimpleGraph (Fin n)).IsCompleteMultipartite", "IsCompleteMultipartite.bot"),
    E("multipartite_bipartite", "complete-multipartite K_{m,n}", "term (property)", "(m n : ℕ)",
      "(completeBipartiteGraph (Fin m) (Fin n)).IsCompleteMultipartite",
      "IsCompleteMultipartite.completeBipartiteGraph _ _"),
    E("egirth_complete", "complete Kₙ", "term + simp (egirth)", "(n : ℕ)",
      "(⊤ : SimpleGraph (Fin (n + 3))).egirth = 3", "egirth_top (by simp)"),
    E("ediam_complete", "complete Kₙ", "simp (ediam)", "(n : ℕ)",
      "(⊤ : SimpleGraph (Fin (n + 2))).ediam = 1", "by simp"),
    E("eccent_complete", "complete Kₙ", "simp (eccentricity)", "(n : ℕ) (v : Fin (n + 2))",
      "(⊤ : SimpleGraph (Fin (n + 2))).eccent v = 1", "by simp"),
    E("degree_complete", "complete Kₙ", "simp (per-vertex degree)", "(n : ℕ) (v : Fin (n + 1))",
      "(⊤ : SimpleGraph (Fin (n + 1))).degree v = n", "by simp"),
    E("egirth_antitone", "egirth monotonicity", "antitone (graph order)",
      "(G G' : SimpleGraph (Fin 5)) (h : G ≤ G')", "G'.egirth ≤ G.egirth", "egirth_anti h"),
    E("cycle_preconnected", "cycle Cₙ", "term (property)", "(n : ℕ)",
      "(cycleGraph n).Preconnected", "cycleGraph_preconnected"),
    E("path_le_cycle", "path/cycle", "term (graph order ≤)", "(n : ℕ)",
      "pathGraph n ≤ cycleGraph n", "pathGraph_le_cycleGraph"),
    E("complete_connected", "complete Kₙ", "simp (connected)", "(n : ℕ)",
      "(⊤ : SimpleGraph (Fin (n + 1))).Connected", "by simp [connected_top_iff] <;> omega"),
    # ── v2.2: harder paradigms — handshake parity, decide, Hasse, Colorable, involution ──
    E("odd_degree_count_even", "any graph (∀G)", "handshake parity (Even count)",
      "(n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]",
      "Even ((univ.filter (fun v => Odd (G.degree v))).card)", "G.even_card_odd_degree_vertices"),
    E("dart_handshake", "any graph (∀G)", "term (dart counting)",
      "(n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]",
      "Fintype.card G.Dart = 2 * G.edgeFinset.card", "G.dart_card_eq_twice_card_edges"),
    E("hasse_cliquefree3", "Hasse diagram", "term (property)", "(n : ℕ)",
      "(hasse (Fin n)).CliqueFree 3", "cliqueFree_hasse_three"),
    E("compl_involution", "complement involution", "term (compl_compl)",
      "(n : ℕ) (G : SimpleGraph (Fin n))", "Gᶜᶜ = G", "compl_compl G"),
    E("colorable_complete", "complete Kₙ", "colorable (coloring)", "(n : ℕ)",
      "(⊤ : SimpleGraph (Fin n)).Colorable n", "⟨⟨id, by simp [Function.onFun]⟩⟩"),
    E("decide_cycle_nonadj", "cycle C₅ (concrete)", "decide", "",
      "¬ (cycleGraph 5).Adj 0 2", "by decide"),
    E("decide_cycle_adj", "cycle C₅ (concrete)", "decide", "",
      "(cycleGraph 5).Adj 0 1", "by decide"),
    E("path2_eq_top", "path P₂ (concrete)", "term (identity)", "",
      "pathGraph 2 = (⊤ : SimpleGraph (Fin 2))", "pathGraph_two_eq_top"),
]

PREAMBLE = "import Mathlib\nopen SimpleGraph Finset\n"


def _mk_proc():
    return ReplProcess(SimpleNamespace(lean_dir=_MATHLIB_LEAN, repl_preamble="import Mathlib"),
                       _REPL_BIN_DEFAULT, restart_every=10 ** 9)

def _check(proc, cmd, timeout=30):
    try:
        r = proc._send({"cmd": cmd, "env": proc.env0}, timeout=timeout)
    except Exception:
        try: proc.start()
        except Exception: pass
        return None
    if any(m.get("severity") == "error" for m in (r.get("messages") or [])):
        return False
    return not r.get("sorries")


def _parametric(e, name):
    return f"theorem {name} {e['binder']} :\n    {e['stmt']} := {e['proof']}"

def generate(out_dir=None, instance_ns=(4, 6, 9), verbose=True):
    out_dir = Path(out_dir) if out_dir else RECORD
    out_dir.mkdir(parents=True, exist_ok=True)
    import shutil
    for d in out_dir.glob("F*"):
        if d.is_dir(): shutil.rmtree(d, ignore_errors=True)
    proc = _mk_proc()
    records, ok_n, n_cand = [], 0, 0

    def write(rid, thm, rec):
        d = out_dir / rid; d.mkdir(exist_ok=True)
        (d / f"{rid}.json").write_text(json.dumps(rec, ensure_ascii=False, indent=2))
        (d / f"{rid}.lean").write_text(PREAMBLE + "\n" + thm + "\n")

    for idx, e in enumerate(CATALOG):
        name = f"F{idx}"
        body = _parametric(e, name)
        ok = _check(proc, "open SimpleGraph Finset\n\n" + body); n_cand += 1
        rec = {"id": name, "domain": "family", "family": e["family"], "kind": "parametric",
               "paradigm": e["paradigm"], "verified_lean": bool(ok),
               "conjecture": {"statement_lean": e["stmt"], "quantifier": "∀"},
               "key": hashlib.sha256(body.encode()).hexdigest()[:12],
               "generator": {"version": "family-B2-2.0"}}
        records.append(rec)
        if verbose:
            print(f"  {name}: {'OK ' if ok else 'xx '} [{e['paradigm']}] {e['family']}", flush=True)
        if not ok:
            continue
        ok_n += 1; write(name, body, rec)
        if not e["inst"]:
            continue
        for N in instance_ns:                           # concrete instances → volume
            iname = f"{name}_n{N}"
            istmt = re.sub(r"\bn\b", str(N), e["stmt"])
            ithm = body + f"\ntheorem {iname} : {istmt} := {name} {e['inst'](N)}"
            iok = _check(proc, "open SimpleGraph Finset\n\n" + ithm); n_cand += 1
            irec = {"id": iname, "domain": "family", "family": e["family"], "kind": "instance",
                    "paradigm": "term-mode (specialize)", "instance_n": N, "instance_of": name,
                    "verified_lean": bool(iok),
                    "conjecture": {"statement_lean": istmt, "quantifier": f"n={N}"},
                    "key": hashlib.sha256(iname.encode()).hexdigest()[:12],
                    "generator": {"version": "family-B2-2.0"}}
            records.append(irec)
            if iok:
                ok_n += 1; write(iname, ithm, irec)
    proc.stop()
    par = Counter(r["paradigm"] for r in records if r["verified_lean"] and r["kind"] == "parametric")
    return {"candidates": n_cand, "verified": ok_n, "all_provable": ok_n == n_cand,
            "families": sorted({e["family"] for e in CATALOG}),
            "distinct_parametric_paradigms": len(par), "paradigms": dict(par),
            "record_dir": str(out_dir)}


if __name__ == "__main__":
    print(json.dumps(generate(), ensure_ascii=False, indent=2))
