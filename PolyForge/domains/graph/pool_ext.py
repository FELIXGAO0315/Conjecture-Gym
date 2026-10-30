"""Extend the screening graph pool beyond the n≤7 atlas.

The base pool (data/graph_pool.json, 1253 graphs, n≤7) is too small to falsify
Barnette-level conjectures — the counterexamples live at larger n (Petersen at n=10,
the Tutte graph at n=46, …).  This builds data/graph_pool_ext.json: famous "hard"
graphs (the actual counterexamples to Tait-type conjectures) plus targeted STRUCTURED
random sampling (cubic / k-regular / bipartite / planar / sparse connected) at n=8..24.

Non-isomorphic de-dup uses pynauty's canonical certificate.  Each graph is stored with
the same feature schema as the base pool (exact where tractable; None for NP-hard
invariants on large graphs — the empirical screener skips a graph for any conjecture whose
required field is None).  Hamiltonicity and planarity are computed at load time from edges.
"""
from __future__ import annotations
import json, random, itertools
from pathlib import Path

import networkx as nx

_HERE = Path(__file__).resolve().parent
OUT = _HERE / "data" / "graph_pool_ext.json"


# ── exact invariants (tractable on sparse / small graphs; None when too costly) ──
NP_HARD_N_CAP = 14          # exact clique / independence / chromatic only for n ≤ this
HAM_STEP_BUDGET = 3_000_000 # Hamiltonicity backtracking budget; None (unknown) if exceeded
# known Hamiltonicity of famous graphs that may exceed the budget (so the key falsifiers
# — Tutte (Tait counterexample), Petersen — are certain)
KNOWN_HAM = {"tutte_graph": False, "petersen_graph": False}

def _ham_budgeted(G):
    """True/False, or None if the search exceeds HAM_STEP_BUDGET (undetermined)."""
    n = G.number_of_nodes()
    if n < 3:
        return False
    G = nx.convert_node_labels_to_integers(G)
    adj = [sorted(G.neighbors(v), key=lambda w: G.degree(w)) for v in range(n)]  # Warnsdorff-ish
    if any(len(a) < 2 for a in adj):
        return False
    seen = [False] * n; seen[0] = True
    steps = [0]
    def dfs(v, cnt):
        steps[0] += 1
        if steps[0] > HAM_STEP_BUDGET:
            raise TimeoutError
        if cnt == n:
            return 0 in adj[v]
        for w in adj[v]:
            if not seen[w]:
                seen[w] = True
                if dfs(w, cnt + 1):
                    return True
                seen[w] = False
        return False
    try:
        return dfs(0, 1)
    except TimeoutError:
        return None

def _planar(G):
    try:
        return nx.check_planarity(G)[0]
    except Exception:
        return None

def _clique_number(G):
    return max((len(c) for c in nx.find_cliques(G)), default=0)

def _chromatic_exact(G, cap=6):
    """Exact χ by trying k = clique-lower-bound .. cap; None if n large or χ > cap."""
    n = G.number_of_nodes()
    if n == 0:
        return 0
    if n > NP_HARD_N_CAP:
        return None
    lo = _clique_number(G)
    for k in range(lo, cap + 1):
        if _k_colorable(G, k):
            return k
    return None

def _k_colorable(G, k):
    nodes = sorted(G.nodes(), key=lambda v: -G.degree(v))
    color = {}
    adj = {v: set(G.neighbors(v)) for v in G.nodes()}
    def bt(i):
        if i == len(nodes):
            return True
        v = nodes[i]
        used = {color[u] for u in adj[v] if u in color}
        for c in range(k):
            if c not in used:
                color[v] = c
                if bt(i + 1):
                    return True
                del color[v]
        return False
    return bt(0)

def _domination_exact(G, cap_n=12):
    n = G.number_of_nodes()
    if n > cap_n:
        return None
    nodes = list(G.nodes())
    closed = {v: {v} | set(G.neighbors(v)) for v in nodes}
    for r in range(1, n + 1):
        for S in itertools.combinations(nodes, r):
            cov = set()
            for v in S:
                cov |= closed[v]
            if len(cov) == n:
                return r
    return n

def _features(G):
    n = G.number_of_nodes()
    G = nx.convert_node_labels_to_integers(G)
    deg = [d for _, d in G.degree()]
    conn = nx.is_connected(G) if n > 0 else False
    acyclic = (G.number_of_edges() == 0) or nx.is_forest(G)
    reg = len(set(deg)) == 1 if deg else False
    clq = _clique_number(G) if n <= NP_HARD_N_CAP else None
    alpha = _clique_number(nx.complement(G)) if n <= NP_HARD_N_CAP else None
    try:
        match = len(nx.max_weight_matching(G))
    except Exception:
        match = None
    girth = None
    if not acyclic:
        try:
            girth = nx.girth(G)
        except Exception:
            girth = None
    return {
        "n": n, "m": G.number_of_edges(),
        "max_degree": max(deg) if deg else 0, "min_degree": min(deg) if deg else 0,
        "chromatic_number": _chromatic_exact(G), "clique_number": clq,
        "independence_number": alpha,
        "vertex_cover_number": (n - alpha) if alpha is not None else None,
        "diameter": (nx.diameter(G) if conn and n > 0 else None),
        "radius": (nx.radius(G) if conn and n > 0 else None),
        "girth": girth,
        "connected": conn, "acyclic": acyclic, "tree": (conn and acyclic),
        "bipartite": nx.is_bipartite(G), "regular": reg,
        "regular_degree": (deg[0] if reg and deg else None),
        "edge_connectivity": (nx.edge_connectivity(G) if n > 1 else 0),
        "vertex_connectivity": (nx.node_connectivity(G) if n > 1 else 0),
        "matching_number": match,
        "domination_number": _domination_exact(G),
        "sum_deg_sq": sum(d * d for d in deg),
        "edges": [list(e) for e in G.edges()],
        "_ham": _ham_budgeted(G), "_planar": _planar(G),
        "source_tag": None,                       # filled by caller
    }


def _cert(G):
    import pynauty
    n = G.number_of_nodes()
    G = nx.convert_node_labels_to_integers(G)
    adj = {v: list(G.neighbors(v)) for v in range(n)}
    return pynauty.certificate(pynauty.Graph(n, directed=False, adjacency_dict=adj))


NAMED = ["petersen_graph", "tutte_graph", "chvatal_graph", "desargues_graph",
         "heawood_graph", "moebius_kantor_graph", "pappus_graph", "frucht_graph",
         "dodecahedral_graph", "icosahedral_graph", "octahedral_graph",
         "sedgewick_maze_graph", "truncated_cube_graph", "truncated_tetrahedron_graph"]


def _candidates(rng, verbose=True):
    """Yield (tag, networkx graph): famous hard graphs + structured random sampling."""
    for name in NAMED:
        try:
            yield name, getattr(nx, name)()
        except Exception:
            pass
    sizes = [8, 9, 10, 12, 14, 16, 18, 20, 24]
    for n in sizes:
        for i in range(24):                                   # cubic (3-regular)
            try: yield f"cubic{n}", nx.random_regular_graph(3, n, seed=rng.randint(0, 10**6))
            except Exception: pass
        for i in range(16):                                   # 4-regular
            try: yield f"reg4_{n}", nx.random_regular_graph(4, n, seed=rng.randint(0, 10**6))
            except Exception: pass
        for i in range(16):                                   # bipartite
            a = rng.randint(3, n // 2); b = n - a
            yield f"bip{n}", nx.bipartite.random_graph(a, b, 0.4, seed=rng.randint(0, 10**6))
        for i in range(12):                                   # sparse connected
            G = nx.gnp_random_graph(n, 2.5 / n, seed=rng.randint(0, 10**6))
            yield f"sparse{n}", G
        for i in range(8):                                    # planar (Delaunay-like via random geometric)
            G = nx.random_geometric_graph(n, 0.55, seed=rng.randint(0, 10**6))
            if nx.check_planarity(G)[0]:
                yield f"planar{n}", G


def build(out=OUT, seed=12345, verbose=True):
    rng = random.Random(seed)
    seen, graphs = set(), []
    n_cand = 0
    for tag, G in _candidates(rng, verbose):
        n_cand += 1
        if G.number_of_nodes() < 3:
            continue
        try:
            c = _cert(G)
        except Exception:
            continue
        if c in seen:
            continue
        seen.add(c)
        f = _features(G)
        f["source_tag"] = tag
        if tag in KNOWN_HAM:                       # certainty for the famous falsifiers
            f["_ham"] = KNOWN_HAM[tag]
        graphs.append(f)
        if verbose and len(graphs) % 50 == 0:
            print(f"  {len(graphs)} distinct graphs ({n_cand} candidates)…", flush=True)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps({"graphs": graphs, "note": "hard + sampled, n up to 24, "
                               "pynauty-deduped; NP-hard invariants None on large graphs"},
                              ensure_ascii=False))
    from collections import Counter
    by_n = Counter(g["n"] for g in graphs)
    print(f"\npool_ext: {len(graphs)} distinct graphs from {n_cand} candidates "
          f"→ {out.name}\n  by n: {dict(sorted(by_n.items()))}", flush=True)
    return {"graphs": len(graphs), "candidates": n_cand, "by_n": dict(sorted(by_n.items()))}


if __name__ == "__main__":
    print(json.dumps(build(), ensure_ascii=False, indent=2))
