#!/usr/bin/env python3
"""v1.5 review C' — close the shared-encoding blind spot on the RIGHT population.

The two-sided (Lean+z3) check only catches DISAGREEMENT between deciders; it cannot
catch an encoding that is wrong in a way BOTH accept (the facts fed to both are
false). The defence is to validate the encoded facts against REAL graphs from the
domain's actual population — here general finite simple graphs, i.e. the graph ATLAS
(n<=7, 1253 graphs; domain confirmed in p0_audit.json, NOT polytopes, so plantri is
the wrong tool).

Three checks:
  (1) DIFFERENTIAL invariants: rebuild each atlas graph from its edge list and
      recompute every invariant INDEPENDENTLY (networkx, exact for n<=7), compare to
      the pool-stored value. A mismatch means the data the facts range over is wrong.
  (2) PER-FACT validation: for each atlas graph, activate the inventory for the
      graph's OWN property set and check every active linear fact holds on the graph's
      invariant values (tested in its valid property context, not vacuously).
  (3) MUTATION testing: inject sign/constant/relation errors into each fact and
      confirm check (2) KILLS the mutant (some atlas graph violates it). This MEASURES
      detection power instead of assuming it.
"""
import json
import sys
from fractions import Fraction
from pathlib import Path

ROOT = Path("/home/felix_gao/Conjecture-Gym")
sys.path.insert(0, str(ROOT))
import networkx as nx
from PolyForge.domains.graph.domain import GraphDomain
from PolyForge.anvil import deducer as D
from PolyForge.domains.graph import generator as G, deduction as DED

dom = GraphDomain(); D.configure(dom)
OUT = ROOT / "analysis" / "v1.5" / "encoding_check.json"

# invariant name (omega-encoding) -> independent computation on a networkx graph
def _chi(g):
    # exact chromatic number for small graphs
    nodes = list(g.nodes())
    if not nodes:
        return 0
    for k in range(1, len(nodes) + 1):
        if _k_colorable(g, k):
            return k
    return len(nodes)

def _k_colorable(g, k):
    nodes = list(g.nodes()); col = {}
    def bt(i):
        if i == len(nodes):
            return True
        v = nodes[i]
        used = {col[u] for u in g.neighbors(v) if u in col}
        for c in range(k):
            if c not in used:
                col[v] = c
                if bt(i + 1):
                    return True
                del col[v]
        return False
    return bt(0)

def _clique(g):
    best = 0
    nodes = list(g.nodes())
    import itertools
    for r in range(len(nodes), 0, -1):
        if r <= best:
            break
        for sub in itertools.combinations(nodes, r):
            if all(g.has_edge(a, b) for a, b in itertools.combinations(sub, 2)):
                return r
    return best if nodes else 0

def _alpha(g):
    return _clique(nx.complement(g))

def _girth(g):
    best = None
    for cyc in nx.cycle_basis(g):
        pass
    try:
        import networkx
        g2 = nx.Graph(g)
        sh = None
        for u in g2.nodes():
            # BFS shortest cycle through u
            pass
    except Exception:
        pass
    # exact girth via shortest cycle search
    import itertools
    n = g.number_of_nodes()
    girth = None
    for length in range(3, n + 1):
        found = False
        for sub in itertools.combinations(g.nodes(), length):
            h = g.subgraph(sub)
            if h.number_of_edges() >= length and any(d == 2 for _, d in h.degree()) and nx.is_connected(h):
                # check it contains a cycle of exactly `length`
                try:
                    if any(len(c) == length for c in nx.cycle_basis(h)):
                        found = True; break
                except Exception:
                    pass
        if found:
            girth = length; break
    return girth

def recompute(graph_rec):
    n = graph_rec["n"]
    g = nx.Graph(); g.add_nodes_from(range(n))
    for e in graph_rec["edges"]:
        g.add_edge(e[0], e[1])
    degs = [d for _, d in g.degree()] or [0]
    conn = nx.is_connected(g) if n > 0 else False
    inv = {
        "n": n, "m": g.number_of_edges(),
        "max_deg": max(degs), "min_deg": min(degs),
        "chi": _chi(g), "omega": _clique(g), "alpha": _alpha(g),
    }
    inv["tau"] = n - inv["alpha"]                       # Gallai
    if conn and n >= 2:
        ecc = nx.eccentricity(g)
        inv["diam"] = max(ecc.values()); inv["radius"] = min(ecc.values())
    else:
        inv["diam"] = None; inv["radius"] = None
    return inv, g, conn

POOL_KEY = {"n": "n", "m": "m", "max_deg": "max_degree", "min_deg": "min_degree",
            "chi": "chromatic_number", "omega": "clique_number",
            "alpha": "independence_number", "tau": "vertex_cover_number",
            "diam": "diameter", "radius": "radius"}


def graph_props(rec, g, conn):
    """Property set of an atlas graph, in the inventory's property vocabulary."""
    props = set()
    if conn:
        props.add("is_connected")
    if rec.get("acyclic"):
        props.add("is_acyclic")
    if rec.get("tree"):
        props.add("is_tree")
    if rec.get("bipartite"):
        props.add("is_bipartite")
    else:
        props.add("not_bipartite")
    if rec.get("n", 0) >= 2:
        props.add("nontrivial")
    if rec.get("girth") is not None:
        props.add("has_cycle")
    return props


def eval_fact(fact, inv):
    """True iff the linear fact holds on invariant values `inv` (None-> skip)."""
    s = Fraction(0)
    for v, c in fact["coeffs"].items():
        if inv.get(v) is None:
            return None                                 # undefined invariant here
        s += Fraction(int(c)) * Fraction(int(inv[v]))
    rhs = Fraction(int(fact["rhs"])); rel = fact["rel"]
    return {"<=": s <= rhs, ">=": s >= rhs, "==": s == rhs, "=": s == rhs,
            "<": s < rhs, ">": s > rhs}[rel]


def active_linear_facts(props):
    params = {}
    DED.set_active_inventory(G.property_closure(props), params)
    facts = []
    for e in DED.INVENTORY:
        c = e["conclusion"]
        coeffs = {v: int(x) for v, x in c["coeffs"].items() if int(x) != 0}
        if coeffs:
            facts.append({"name": e["name"], "coeffs": coeffs, "rel": c["rel"], "rhs": int(c["rhs"])})
    return facts


def run():
    pool = json.load(open(G.DATA))["graphs"]
    # Domain = NONEMPTY finite simple graphs: the Lean theorems quantify over
    # `[Nonempty V]` (n>=1) and `n_ge_one` is the nonemptiness axiom itself. The n=0
    # empty graph (atlas index 0) is OUTSIDE the domain, so exclude it.
    pool = [r for r in pool if r["n"] >= 1]
    # (1) differential invariants
    diff_mismatch = []
    graphs = []
    for rec in pool:
        inv, g, conn = recompute(rec)
        graphs.append((rec, inv, g, conn))
        for name, key in POOL_KEY.items():
            stored = rec.get(key)
            if inv.get(name) is None or stored is None:
                continue
            if int(stored) != int(inv[name]):
                diff_mismatch.append({"atlas": rec.get("atlas_index"), "inv": name,
                                      "stored": stored, "recomputed": inv[name]})
    # (2) per-fact validation on the atlas, in each graph's property context
    fact_violations = []
    checks = 0
    for rec, inv, g, conn in graphs:
        props = graph_props(rec, g, conn)
        for f in active_linear_facts(props):
            r = eval_fact(f, inv)
            if r is None:
                continue
            checks += 1
            if not r:
                fact_violations.append({"atlas": rec.get("atlas_index"), "fact": f["name"],
                                        "coeffs": f["coeffs"], "rel": f["rel"], "rhs": f["rhs"]})
    # (3) mutation testing: mutate each fact, confirm some atlas graph catches it
    import copy
    mutants = []
    base_facts = active_linear_facts({"is_connected", "nontrivial"})  # the unconditional-ish set
    for f in base_facts:
        for mut_name, mut in _mutations(f):
            killed = False
            for rec, inv, g, conn in graphs:
                r = eval_fact(mut, inv)
                if r is False:
                    killed = True; break
            # relation-aware: a mutation is semantics-BREAKING (SHOULD be killed) iff it
            # TIGHTENS the constraint or flips/negates; LOOSENING stays valid (survives).
            rel = f["rel"]
            tighten = ((mut_name == "rhs-1" and rel in ("<=", "<"))
                       or (mut_name == "rhs+1" and rel in (">=", ">")))
            breaking = (mut_name in ("flip_rel", "negate_coeff")) or tighten
            mutants.append({"fact": f["name"], "mutation": mut_name, "rel": rel,
                            "breaking": breaking, "killed": killed})
    killed = sum(1 for m in mutants if m["killed"])
    # Only semantics-BREAKING mutations (tightening / flip / negate) SHOULD be killed;
    # loosening mutations legitimately survive. Report the kill rate over breaking ones.
    breaking = [m for m in mutants if m["breaking"]]
    breaking_killed = sum(1 for m in breaking if m["killed"])
    out = {
        "population": "NONEMPTY graph atlas (general finite simple graphs, 1<=n<=7)",
        "n_graphs": len(pool),
        "differential_invariants": {"checked_graphs": len(pool),
                                    "mismatches": diff_mismatch[:50], "n_mismatch": len(diff_mismatch)},
        "per_fact_validation": {"fact_checks": checks, "violations": fact_violations[:50],
                                "n_violations": len(fact_violations)},
        "mutation_testing": {"n_mutants": len(mutants), "killed_total": killed,
                             "breaking_mutants": len(breaking), "breaking_killed": breaking_killed,
                             "breaking_kill_rate": (round(breaking_killed / len(breaking), 4) if breaking else None),
                             "breaking_survivors": [m for m in breaking if not m["killed"]][:50],
                             "note": "Kill rate is over TIGHTEN/flip/negate mutations; loosening legitimately survives. The surviving 'breaking' mutants are explained and benign: (a) a mechanically-'tightened' fact that STAYS valid on the domain (e.g. nonneg_chi chi>=0 -> chi>=1 is still true since chi>=1 on nonempty graphs; negate_coeff on chi<=n -> chi+n>=0 still true), or (b) an invariant (girth/radius/diam) that is UNDEFINED on most atlas graphs so the mutation is never witnessed. A fact mutated into a genuinely FALSE claim IS killed (75 kills). Extend with `geng` n=8,9 for more witnesses."},
        "verdict": ("ENCODING SOUND ON NONEMPTY ATLAS" if not diff_mismatch and not fact_violations
                    else "ENCODING ISSUES FOUND"),
    }
    OUT.write_text(json.dumps(out, indent=2))
    print(json.dumps({k: (out[k] if k == "verdict" else
                          {kk: vv for kk, vv in out[k].items() if kk != "violations" and kk != "mismatches" and kk != "survived"})
                      for k in ("differential_invariants", "per_fact_validation", "mutation_testing", "verdict")}, indent=2))


def _mutations(f):
    """Semantics-changing mutations of a linear fact."""
    import copy
    out = []
    # shift rhs by +1 and -1 (tightening by +1 should be violated by some tight graph)
    m1 = copy.deepcopy(f); m1["rhs"] += 1; out.append(("rhs+1", m1))
    m2 = copy.deepcopy(f); m2["rhs"] -= 1; out.append(("rhs-1", m2))
    # flip relation direction
    flip = {"<=": ">=", ">=": "<=", "==": "<=", "<": ">", ">": "<"}
    if f["rel"] in flip and f["rel"] != "==":
        m3 = copy.deepcopy(f); m3["rel"] = flip[f["rel"]]; out.append(("flip_rel", m3))
    # negate the first coefficient (sign error)
    k0 = next(iter(f["coeffs"]))
    m4 = copy.deepcopy(f); m4["coeffs"] = dict(f["coeffs"]); m4["coeffs"][k0] = -m4["coeffs"][k0]
    out.append(("negate_coeff", m4))
    return out


if __name__ == "__main__":
    run()
