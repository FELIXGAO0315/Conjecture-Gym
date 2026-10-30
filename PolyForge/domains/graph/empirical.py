"""Empirical structural-conjecture generator (PolyForge — mode C, "Barnette-level").

A THIRD carrier.  The LP engine and the structural engine both produce *verified*
theorems — bounded by what can be proved automatically, so they cannot reach the level
of Barnette's conjecture (an OPEN problem: no proof exists to find).  This mode drops the
"auto-proved" requirement and instead GENERATES CONJECTURES and screens them for
falsification against a graph database — exactly how automated conjecture-making systems
(Graffiti, …) and human mathematicians propose new results.

Each conjecture is a structural implication
    ∀ G,  (P₁ G ∧ … ∧ P_k G)  →  Q G
over graph *classes* (connected, bipartite, cubic/regular, k-connected, planar,
girth/degree bounds, …) with a deep structural conclusion (Hamiltonian, has a perfect
matching, k-colorable, planar, …).  It is screened against every graph in the pool
(n ≤ POOL_N_MAX); Hamiltonicity and planarity — absent from the pool and from Mathlib —
are computed here from the edge lists.  A conjecture is KEPT iff:

  * it has no counterexample in the pool,            (empirically true so far)
  * its support is non-trivial (≥ MIN_SUPPORT),      (not vacuous)
  * it is IRREDUNDANT: dropping ANY single hypothesis breaks it,   (every P_i earns its place)
  * the conclusion is not already forced with no hypotheses.       (non-trivial)

Kept conjectures are UNPROVEN (flagged `status: "empirical"`).  They are the output the
north star actually asks for — hard, genuine conjectures — not proofs.
"""
from __future__ import annotations
import json, itertools, hashlib
from pathlib import Path
from collections import Counter

_HERE = Path(__file__).resolve().parent
_ROOT = _HERE.parents[2]                        # repo root (Conjecture-Gym)
POOL = _HERE / "data" / "graph_pool.json"
POOL_EXT = _HERE / "data" / "graph_pool_ext.json"   # hard + sampled graphs, n up to 24/46
RECORD = _HERE / "record_empirical"            # S* → E* (empirical conjectures)
OPEN_OUT = _ROOT / "output" / "open_conjectures.jsonl"   # the UNPROVEN conjecture bank

MIN_SUPPORT = 3            # ≥ this many pool graphs must satisfy the hypotheses
MAX_HYPS = 3              # hypothesis-combination size


# ── computed predicates (not in the pool): Hamiltonicity, planarity ──────────────
def _is_hamiltonian(g) -> bool:
    n = g["n"]
    if n < 3:
        return False
    adj = [set() for _ in range(n)]
    for a, b in g["edges"]:
        adj[a].add(b); adj[b].add(a)
    seen = [False] * n; seen[0] = True
    def dfs(v, cnt):
        if cnt == n:
            return 0 in adj[v]
        for w in adj[v]:
            if not seen[w]:
                seen[w] = True
                if dfs(w, cnt + 1):
                    return True
                seen[w] = False
        return False
    return dfs(0, 1)

def _is_planar(g):
    try:
        import networkx as nx
        G = nx.Graph(); G.add_nodes_from(range(g["n"])); G.add_edges_from(g["edges"])
        return nx.check_planarity(G)[0]
    except Exception:
        return None


def load_pool():
    """Base (n≤7 exhaustive) + extended (hard + sampled, n up to 46) screening pool.
    Hamiltonicity/planarity: use the extended pool's precomputed `_ham`/`_planar`
    (budgeted at build time; may be None = undetermined); compute for the small base
    graphs (always fast)."""
    pool = json.load(open(POOL))["graphs"]
    if POOL_EXT.exists():
        pool = pool + json.load(open(POOL_EXT))["graphs"]
    for g in pool:
        if "_ham" not in g:
            g["_ham"] = _is_hamiltonian(g)
        if "_planar" not in g:
            g["_planar"] = _is_planar(g)
    return pool


# ── predicate & conclusion library (each: key, human-text, lambda over pool dict) ──
# `lean` is a best-effort Lean predicate on `G` (None where Mathlib can't express it, e.g. planar).
def _P(key, text, fn, lean=None):
    return dict(key=key, text=text, fn=fn, lean=lean)

HYPOTHESES = [
    _P("connected", "connected", lambda g: g["connected"], "G.Connected"),
    _P("bipartite", "bipartite", lambda g: g["bipartite"], "G.IsBipartite"),
    _P("triangle_free", "triangle-free", lambda g: g["clique_number"] < 3, "G.CliqueFree 3"),
    _P("regular", "regular", lambda g: g["regular"], None),
    _P("cubic", "cubic (3-regular)", lambda g: g["regular_degree"] == 3, None),
    _P("k2_connected", "2-connected", lambda g: g["vertex_connectivity"] >= 2, None),
    _P("k3_connected", "3-connected", lambda g: g["vertex_connectivity"] >= 3, None),
    _P("planar", "planar", lambda g: g["_planar"], None),
    _P("mindeg_ge3", "min degree ≥ 3", lambda g: g["min_degree"] >= 3, None),
    _P("girth_ge4", "girth ≥ 4", lambda g: g["girth"] is None or g["girth"] >= 4, None),
    _P("dirac", "min degree ≥ n/2", lambda g: 2 * g["min_degree"] >= g["n"], None),
]

CONCLUSIONS = [
    _P("hamiltonian", "Hamiltonian", lambda g: g["_ham"], None),
    _P("has_perfect_matching", "has a perfect matching",
       lambda g: 2 * g["matching_number"] == g["n"], None),
    _P("three_colorable", "3-colorable", lambda g: g["chromatic_number"] <= 3, "G.Colorable 3"),
    _P("planar", "planar", lambda g: g["_planar"], None),
    _P("connected", "connected", lambda g: g["connected"], "G.Connected"),
]


def _eval(fn, g):
    """Evaluate a predicate on a graph → True / False / None (None = undetermined:
    a needed field is missing/None, so this graph can't be used for this predicate)."""
    try:
        v = fn(g)
    except (TypeError, KeyError):
        return None
    return None if v is None else bool(v)

def _applies(hyps, g):
    """True only if EVERY hypothesis is determined and holds (None → graph excluded)."""
    return all(_eval(h["fn"], g) is True for h in hyps)

def screen(hyps, concl, pool):
    """(support, counterexamples) for ∀G (⋀hyps → concl).  Graphs where the conclusion
    is undetermined (None) are excluded from BOTH counts — never a spurious counterexample."""
    sat = [g for g in pool if _applies(hyps, g)]
    decided = [(g, _eval(concl["fn"], g)) for g in sat]
    decided = [(g, v) for g, v in decided if v is not None]
    ce = [g for g, v in decided if v is False]
    return len(decided), len(ce)

def _irredundant(hyps, concl, pool):
    """Every hypothesis is necessary: dropping any one introduces a counterexample
    (so the conjecture is not 'carried' by a sub-combination)."""
    if len(hyps) < 2:
        return True
    for i in range(len(hyps)):
        sub = hyps[:i] + hyps[i + 1:]
        _, ce = screen(sub, concl, pool)
        if ce == 0:                 # sub-combo already forces the conclusion → hyp i redundant
            return False
    return True

def _nontrivial(concl, pool):
    """Conclusion is not already true for (almost) all graphs with no hypothesis."""
    sup, ce = screen([], concl, pool)
    return ce > 0                   # some graph violates concl → concl is a real restriction


def generate(out_dir=None, verbose=True, min_support=MIN_SUPPORT, max_hyps=MAX_HYPS):
    out_dir = Path(out_dir) if out_dir else RECORD
    out_dir.mkdir(parents=True, exist_ok=True)
    import shutil
    for d in out_dir.glob("E*"):
        if d.is_dir():
            shutil.rmtree(d, ignore_errors=True)
    pool = load_pool()
    pool_n_max = max(g["n"] for g in pool)
    kept, n_screened = [], 0

    for concl in CONCLUSIONS:
        if not _nontrivial(concl, pool):
            continue
        usable = [h for h in HYPOTHESES if h["key"] != concl["key"]]
        for k in range(1, max_hyps + 1):
            for combo in itertools.combinations(usable, k):
                n_screened += 1
                sup, ce = screen(list(combo), concl, pool)
                if ce != 0 or sup < min_support:
                    continue
                if not _irredundant(list(combo), concl, pool):
                    continue
                kept.append((list(combo), concl, sup))

    # prefer the strongest/most-supported; difficulty by #hyps + conclusion depth
    CONCL_DEPTH = {"hamiltonian": 3.0, "has_perfect_matching": 2.5, "planar": 2.5,
                   "three_colorable": 1.5, "connected": 1.0}
    records = []
    for idx, (hyps, concl, sup) in enumerate(kept):
        rid = f"E{idx}"
        hyp_txt = " ∧ ".join(h["text"] for h in hyps)
        nl = f"∀ G,  {hyp_txt}  →  {concl['text']}"
        statable = all(h["lean"] for h in hyps) and concl["lean"]
        lean_stmt = None
        if statable:
            prem = " → ".join(h["lean"] for h in hyps)
            lean_stmt = f"∀ (G : SimpleGraph V) [DecidableRel G.Adj], {prem} → {concl['lean']}"
        difficulty = round(len(hyps) + CONCL_DEPTH.get(concl["key"], 1.0)
                           + 0.01 * sup, 3)
        rec = {"id": rid, "domain": "graph-empirical", "kind": "empirical-conjecture",
               "conjecture_type": f"structural class → {concl['text']}",
               "status": "empirical",                 # UNPROVEN: no counterexample for n ≤ 7
               "hypotheses": [h["key"] for h in hyps], "conclusion": concl["key"],
               "support": sup, "screened_up_to_n": pool_n_max,
               "difficulty": difficulty,
               "nl": nl, "statement_lean": lean_stmt, "lean_expressible": bool(statable),
               "key": hashlib.sha256(nl.encode()).hexdigest()[:12],
               "generator": {"version": "empirical-C-0.1"}}
        records.append(rec)
        d = out_dir / rid; d.mkdir(exist_ok=True)
        (d / f"{rid}.json").write_text(json.dumps(rec, ensure_ascii=False, indent=2))
        if verbose:
            mark = "⟦Lean⟧" if statable else "⟦n≤7⟧"
            print(f"  {rid}: {mark} (sup={sup:3}, d={difficulty:4}) {nl}", flush=True)

    # consolidated UNPROVEN conjecture bank (kept separate from train_corpus.jsonl —
    # these have no proof, so they must never be fed to the prover as proof targets).
    OPEN_OUT.parent.mkdir(parents=True, exist_ok=True)
    with open(OPEN_OUT, "w") as f:
        for r in records:
            f.write(json.dumps(r, ensure_ascii=False) + "\n")
    if verbose:
        print(f"  → {len(records)} open conjectures → {OPEN_OUT.relative_to(_ROOT)}", flush=True)

    by_concl = Counter(r["conclusion"] for r in records)
    return {"screened": n_screened, "kept": len(records),
            "by_conclusion": dict(by_concl),
            "lean_expressible": sum(1 for r in records if r["lean_expressible"]),
            "open_bank": str(OPEN_OUT), "record_dir": str(out_dir)}


if __name__ == "__main__":
    print(json.dumps(generate(), ensure_ascii=False, indent=2))
