#!/usr/bin/env python3
"""PolyForge v1.4.5 §V/§M/§C: validation + minimality/cost analysis tools for the
complete-usability closure checker (audit-only; no record/generation/pruning change).

Graph counterexample checks reuse the generator's OWN invariant/property/matching
functions (``_graph_matches``, ``INV.properties_of``, ``DED.vars_from_graph``) so the
conventions match the pipeline's refutation exactly.  Entailment/usability reuse
``closure_complete`` (Lean omega).  Usability uses the restricted (product-free)
Inventory and the property-implication lattice, consistent with the documented
redundancy criterion (README: premise implication "never a product").
"""
import json, sys
from collections import defaultdict
from pathlib import Path

sys.path.insert(0, "/home/felix_gao/Conjecture-Gym")
from PolyForge.domains.graph.domain import GraphDomain
from PolyForge.anvil import deducer as D
from PolyForge.domains.graph import generator as G
from PolyForge.domains.graph import inventory as INV
from PolyForge.env import closure_complete as CC

dom = GraphDomain(); D.configure(dom)


# ── V0: graph sets (the generator's own pool = the networkx atlas, precomputed) ──
def pool_graphs(exclude_zero=True):
    pool = json.load(open(G.DATA))["graphs"]
    gs = [g for g in pool if not (exclude_zero and g["n"] == 0)]
    return [(g, INV.properties_of(g)) for g in gs]


def satisfies(g, gprops, props, numeric):
    """Generator's own 'graph g satisfies these premises' test (handles parametric
    is_regular / is_k_edge_connected and None-valued invariants exactly as the
    pipeline refutation does)."""
    return G._graph_matches(g, gprops, props, numeric)


# ── V2: counterexample cross-check for a usable (T, R) pair ──────────────────────
def witness_T_not_R(graphs, Tprops, Tnum, Rprops, Rnum):
    """Return a graph (atlas_index) satisfying T's premises but VIOLATING R's premises,
    else None.  A usable pair (premises(T) ⊨ premises(R)) must have NO such witness."""
    for g, gp in graphs:
        if satisfies(g, gp, Tprops, Tnum) and not satisfies(g, gp, Rprops, Rnum):
            return g
    return None


# ── V3: property lattice verification + missing-implication scan ─────────────────
_PROP_NAMES = ["is_connected", "is_tree", "is_acyclic", "is_bipartite", "not_bipartite",
               "has_cycle", "is_regular", "nontrivial"]


def lattice_closure_pairs():
    """All (ante, cons) implications entailed by INV.IMPLICATIONS (transitive)."""
    out = set()
    for a in _PROP_NAMES:
        clo = G.property_closure({a})
        for c in clo:
            if c != a:
                out.add((a, c))
    return out


def verify_lattice(graphs):
    """For each implication in the (transitive) lattice, check it holds on every graph.
    Also scan all (ante, cons) property pairs for implications that hold on EVERY graph
    but are absent from the lattice (possible incompleteness, not bugs)."""
    coded = lattice_closure_pairs()
    violated = []
    for (a, c) in sorted(coded):
        for g, gp in graphs:
            if gp.get(a) and not gp.get(c):
                violated.append({"impl": [a, c], "atlas_index": g.get("atlas_index")}); break
    # universal implications among single properties (excluding parametric is_regular on cons)
    missing = []
    for a in _PROP_NAMES:
        for c in _PROP_NAMES:
            if a == c or (a, c) in coded:
                continue
            holds = True; support = 0
            for g, gp in graphs:
                if gp.get(a):
                    support += 1
                    if not gp.get(c):
                        holds = False; break
            if holds and support > 0:
                missing.append({"impl": [a, c], "support": support})
    return {"coded_implications": sorted(list(map(list, coded))),
            "violations": violated, "missing_but_universal": missing}


# ── batched omega (chunked so a single Lean file never grows unbounded) ──────────
def omega_chunked(cases, chunk=1200):
    import os as _os, time as _t
    out = {}
    n = len(cases); t0 = _t.time(); nchunks = (n + chunk - 1) // chunk
    for ci, i in enumerate(range(0, n, chunk)):
        part = cases[i:i + chunk]
        dec, _s, _l = CC.omega_decide_batch(part)
        out.update(dec)
        if _os.environ.get("PF_HEARTBEAT"):
            el = _t.time() - t0
            done = ci + 1
            eta = (el / done) * (nchunks - done) if done else 0.0
            print(f"[omega_chunked] chunk {done}/{nchunks} ({len(out)}/{n} goals) "
                  f"elapsed={el:.0f}s eta={eta:.0f}s", flush=True)
    return out


# ── complete-sense usability + redundancy (same two-step definition; complete) ───
def _sig(props, numeric):
    pk = tuple(sorted((p["name"], p.get("param")) for p in props))
    nk = tuple(sorted((tuple(sorted(pr["coeffs"].items())), pr["rel"], int(pr["rhs"])) for pr in numeric))
    return (pk, nk)


def sat_set(graphs, props, numeric, _cache={}):
    """Set of atlas_index of graphs satisfying (props, numeric), memoised by signature.
    Used for the Lean-independent counterexample cross-check (sound usability ⇒
    sat(T) ⊆ sat(R))."""
    key = _sig(props, numeric)
    if key not in _cache:
        _cache[key] = frozenset(g["atlas_index"] for g, gp in graphs if satisfies(g, gp, props, numeric))
    return _cache[key]


def base_facts(props, numeric):
    """(pset, base) where base = restricted active inventory ∪ numeric premises, as
    omega fact tuples; conditionals returned separately for fixpoint firing."""
    params = {p["name"]: p.get("param") for p in props if "param" in p}
    pset, inv, conds = CC.active_restricted_facts(props, params)
    base = [CC._ptuple(pr) for pr in numeric] + inv
    return pset, base, conds


def usable_matrix(targets, context_views, exclude_self=True):
    """targets: list of view dicts (id/props/numeric/canon/disp); context_views: candidates.
    Returns (usable: {tid: set(rid)}, bases: {tid: (pset, base, conds)}).  R usable for T
    iff R.props ⊆ pset(T) (lattice via property_closure) AND omega proves each numeric
    premise of R from base(T).  Self-excluded by id when exclude_self."""
    bases = {}
    cases = []
    prelim = defaultdict(set)   # tid -> rids passing property subset (+ empty-numeric auto)
    pending = defaultdict(dict)  # tid -> {rid: [case_names]}
    for T in targets:
        tid = T["id"]
        pset, base, conds = base_facts(T["props"], T["numeric"])
        bases[tid] = (pset, base, conds)
        tvars = sorted({v for f in base for v in f[0]})
        for R in context_views:
            rid = R["id"]
            if rid is None or (exclude_self and rid == tid):
                continue
            if not CC.props_dischargeable(R["props"], T["props"], pset):
                continue
            if not R["numeric"]:
                prelim[tid].add(rid); continue
            names = []
            for j, pr in enumerate(R["numeric"]):
                g = CC._ptuple(pr); vs = sorted(set(tvars) | set(g[0]))
                nm = f"U::{tid}::{rid}::{j}"
                cases.append((nm, base, g, vs)); names.append(nm)
            pending[tid][rid] = names
    dec = omega_chunked(cases)
    usable = {T["id"]: set(prelim[T["id"]]) for T in targets}
    for tid, rmap in pending.items():
        for rid, names in rmap.items():
            if all(dec.get(n, False) for n in names):
                usable[tid].add(rid)
    return usable, bases


def entailment_cases(targets, usable, bases, view_by_id, with_records=True):
    """Build omega goal cases: base(T) [+ usable record disp conclusions] ⊨ canon(T).
    with_records=False ⇒ inventory-only (step 1)."""
    cases = []
    for T in targets:
        tid = T["id"]; pset, base, conds = bases[tid]
        facts = list(base)
        if with_records:
            for rid in usable[tid]:
                d = view_by_id[rid]["disp"]
                facts.append(({v: int(c) for v, c in d["coeffs"].items() if int(c) != 0},
                              CC._norm(d["rel"]), int(d["rhs"])))
        # fire conditionals completely (fixpoint) — small, do inline per T
        facts = _fire_conditionals(facts, conds)
        canon = T["canon"]
        goal = ({v: int(c) for v, c in canon["coeffs"].items() if int(c) != 0}, canon["rel"], int(canon["rhs"]))
        vs = sorted({v for f in facts for v in f[0]} | set(goal[0]))
        cases.append((f"G::{tid}", facts, goal, vs))
    return cases


def _fire_conditionals(facts, conds):
    present = {(tuple(sorted(c.items())), r, h) for (c, r, h) in facts}
    changed = True
    while changed:
        changed = False
        for (hyp, concl) in conds:
            key = (tuple(sorted(concl[0].items())), concl[1], concl[2])
            if key in present or not concl[0]:
                continue
            vs = sorted({v for f in facts for v in f[0]} | set(hyp[0]))
            if CC.omega_decide_batch([("h", facts, hyp, vs)])[0]["h"]:
                facts.append(concl); present.add(key); changed = True
    return facts
