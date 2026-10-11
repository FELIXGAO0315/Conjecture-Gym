"""Graph-domain linear Inventory (PolyForge v1.1, stage 1).

The axiom base the deduction engine reasons over for the graph domain: linear
relations among graph invariants, each backed by a Mathlib theorem or a
self-proved lemma in ``GraphLemmas.lean``.  Conclusions are linear (in)equalities
over the invariant variables; graph *properties* (connected, tree, …) appear only
as applicability conditions, never as numeric terms.

Variables (all ℕ-valued; see ``GraphLemmas.lean`` for the ℕ∞→ℕ ``toNat`` facts):

    n        number of vertices        Fintype.card V
    m        number of edges           G.edgeFinset.card
    max_deg  maximum degree            G.maxDegree
    min_deg  minimum degree            G.minDegree
    chi      chromatic number          G.chromaticNumber.toNat
    omega    clique number             G.cliqueNum
    alpha    independence number       G.indepNum
    tau      vertex-cover number       G.vertexCoverNum.toNat
    diam     diameter                  G.diam            (finite iff connected)
    radius   radius                    G.radius.toNat    (finite iff connected)
    girth    girth                     G.girth           (finite iff has a cycle)

Finiteness restrictions (§I.2) — a variable may appear in a premise, conclusion
or proof only when its finiteness condition is met:

    diam, radius : require ``is_connected``   (ediam/radius = ⊤ otherwise)
    girth        : require ``has_cycle``      (egirth = ⊤ when acyclic)
    chi, tau     : always finite for a finite graph (via toNat)

Each inventory entry carries:
    name, lean_name, source ("Mathlib" | "GraphLemmas"),
    properties : graph properties that must hold (or follow by the implication
                 rules) for the entry to be usable,
    finite     : variables whose finiteness must hold (gated by `properties`),
    guards     : extra numeric side conditions {coeffs, rel, rhs} (e.g. n ≥ 1),
    param      : None | "d" (regular degree) | "k" (edge-connectivity),
    conclusion : {coeffs, rel, rhs}  meaning  Σ coeffs·var  rel  rhs.
"""

from __future__ import annotations

from fractions import Fraction

# ── variables ────────────────────────────────────────────────────────────────
VARS = ["n", "m", "max_deg", "min_deg", "chi", "omega", "alpha", "tau",
        "diam", "radius", "girth"]

# variables whose finiteness is conditional, and the property that grants it
FINITENESS = {
    "diam": "is_connected",
    "radius": "is_connected",
    "girth": "has_cycle",
}

# ── properties (§II.1) ────────────────────────────────────────────────────────
PROPERTIES = [
    "is_connected", "is_tree", "is_acyclic", "is_bipartite", "not_bipartite",
    "has_cycle", "is_regular", "is_k_edge_connected", "nontrivial",
]

# ── property implication rules (§II.2), with Lean basis ───────────────────────
# Each rule: (antecedent property, [consequent properties], lean_basis).
IMPLICATIONS = [
    ("is_tree", ["is_connected", "is_acyclic"],
     "SimpleGraph.IsTree.isConnected / IsTree.isAcyclic (IsTree := connected ∧ acyclic)"),
    ("is_acyclic", ["is_bipartite"],
     "SimpleGraph.IsAcyclic.chromaticNumber_le_two + chromaticNumber_le_two_iff_isBipartite"),
    ("has_cycle", ["nontrivial"],
     "PolyForge.Graph.hasCycle_two_le_card (¬IsAcyclic ⟹ 2 ≤ card V)"),  # v1.1.2 §II.2
]
# Mutual exclusion: has_cycle ⟺ ¬ is_acyclic  (SimpleGraph.girth: egirth_eq_top ↔ IsAcyclic)
EXCLUSIVE = [("has_cycle", "is_acyclic")]
# Bipartite ⟺ chi ≤ 2 ; not_bipartite ⟺ chi ≥ 3 (SimpleGraph.chromaticNumber_le_two_iff_isBipartite).
# Implemented as a chi threshold split at 2/3 by the deduction engine (§II.3).
BIPARTITE_CHI = {"is_bipartite": ("chi", "<=", 2), "not_bipartite": ("chi", ">=", 3)}


def _lin(**terms):
    return {v: Fraction(c) for v, c in terms.items() if Fraction(c) != 0}


# ── inventory entries ─────────────────────────────────────────────────────────
INVENTORY = [
    # 1 — ω ≤ χ
    {"name": "omega_le_chi", "lean_name": "SimpleGraph.cliqueNum_le_chromaticNumber",
     "source": "Mathlib", "properties": [], "finite": [], "guards": [], "param": None,
     "conclusion": {"coeffs": _lin(omega=1, chi=-1), "rel": "<=", "rhs": 0}},
    # 2 — χ ≤ n
    {"name": "chi_le_n", "lean_name": "SimpleGraph.chromaticNumber_le_card",
     "source": "Mathlib", "properties": [], "finite": [], "guards": [], "param": None,
     "conclusion": {"coeffs": _lin(chi=1, n=-1), "rel": "<=", "rhs": 0}},
    # 3 — min_deg ≤ max_deg
    {"name": "min_le_max", "lean_name": "SimpleGraph.minDegree_le_maxDegree",
     "source": "Mathlib", "properties": [], "finite": [], "guards": [], "param": None,
     "conclusion": {"coeffs": _lin(min_deg=1, max_deg=-1), "rel": "<=", "rhs": 0}},
    # 4 — max_deg ≤ n − 1  (n ≥ 1)
    {"name": "max_lt_card", "lean_name": "SimpleGraph.maxDegree_lt_card_verts",
     "source": "Mathlib", "properties": [], "finite": [],
     "guards": [{"coeffs": _lin(n=1), "rel": ">=", "rhs": 1}], "param": None,
     "conclusion": {"coeffs": _lin(max_deg=1, n=-1), "rel": "<=", "rhs": -1}},
    # 5 — max_deg ≤ m   (GraphLemmas, v1.0)
    {"name": "max_le_edges", "lean_name": "PolyForge.Graph.maxDegree_le_card_edgeFinset",
     "source": "GraphLemmas", "properties": [], "finite": [], "guards": [], "param": None,
     "conclusion": {"coeffs": _lin(max_deg=1, m=-1), "rel": "<=", "rhs": 0}},
    # 6 — tau ≤ n − 1  (n ≥ 1)
    {"name": "tau_le_card_sub_one", "lean_name": "PolyForge.Graph.vertexCoverNum_toNat_le_card_sub_one",
     "source": "GraphLemmas", "properties": [], "finite": [],
     "guards": [{"coeffs": _lin(n=1), "rel": ">=", "rhs": 1}], "param": None,
     "conclusion": {"coeffs": _lin(tau=1, n=-1), "rel": "<=", "rhs": -1}},
    # 7 — alpha + tau = n   (Gallai, GraphLemmas)
    {"name": "gallai", "lean_name": "PolyForge.Graph.indepNum_add_vertexCoverNum_toNat",
     "source": "GraphLemmas", "properties": [], "finite": [], "guards": [], "param": None,
     "conclusion": {"coeffs": _lin(alpha=1, tau=1, n=-1), "rel": "=", "rhs": 0}},
    # 8a — chi ≥ 1  (n ≥ 1)
    {"name": "chi_ge_one", "lean_name": "PolyForge.Graph.one_le_chromaticNumber_toNat",
     "source": "GraphLemmas", "properties": [], "finite": [],
     "guards": [{"coeffs": _lin(n=1), "rel": ">=", "rhs": 1}], "param": None,
     "conclusion": {"coeffs": _lin(chi=1), "rel": ">=", "rhs": 1}},
    # 8b — omega ≥ 1  (n ≥ 1)
    {"name": "omega_ge_one", "lean_name": "PolyForge.Graph.one_le_cliqueNum",
     "source": "GraphLemmas", "properties": [], "finite": [],
     "guards": [{"coeffs": _lin(n=1), "rel": ">=", "rhs": 1}], "param": None,
     "conclusion": {"coeffs": _lin(omega=1), "rel": ">=", "rhs": 1}},
    # 8c — alpha ≥ 1  (n ≥ 1)
    {"name": "alpha_ge_one", "lean_name": "PolyForge.Graph.one_le_indepNum",
     "source": "GraphLemmas", "properties": [], "finite": [],
     "guards": [{"coeffs": _lin(n=1), "rel": ">=", "rhs": 1}], "param": None,
     "conclusion": {"coeffs": _lin(alpha=1), "rel": ">=", "rhs": 1}},
    # 9a — radius ≤ diam   (connected)
    {"name": "radius_le_diam", "lean_name": "PolyForge.Graph.radius_toNat_le_diam",
     "source": "GraphLemmas", "properties": ["is_connected"], "finite": ["radius", "diam"],
     "guards": [], "param": None,
     "conclusion": {"coeffs": _lin(radius=1, diam=-1), "rel": "<=", "rhs": 0}},
    # 9b — diam ≤ 2·radius   (connected)
    {"name": "diam_le_two_radius", "lean_name": "PolyForge.Graph.diam_le_two_mul_radius_toNat",
     "source": "GraphLemmas", "properties": ["is_connected"], "finite": ["radius", "diam"],
     "guards": [], "param": None,
     "conclusion": {"coeffs": _lin(diam=1, radius=-2), "rel": "<=", "rhs": 0}},
    # 10 — is_tree : m = n − 1
    {"name": "tree_edges", "lean_name": "SimpleGraph.IsTree.card_edgeFinset",
     "source": "Mathlib", "properties": ["is_tree"], "finite": [], "guards": [], "param": None,
     "conclusion": {"coeffs": _lin(m=1, n=-1), "rel": "=", "rhs": -1}},
    # 11 — is_tree ∧ nontrivial : min_deg = 1
    {"name": "tree_min_deg", "lean_name": "SimpleGraph.IsTree.minDegree_eq_one_of_nontrivial",
     "source": "Mathlib", "properties": ["is_tree", "nontrivial"], "finite": [],
     "guards": [], "param": None,
     "conclusion": {"coeffs": _lin(min_deg=1), "rel": "=", "rhs": 1}},
    # 12 — is_acyclic : chi ≤ 2
    {"name": "acyclic_chi", "lean_name": "SimpleGraph.IsAcyclic.chromaticNumber_le_two",
     "source": "Mathlib", "properties": ["is_acyclic"], "finite": [], "guards": [], "param": None,
     "conclusion": {"coeffs": _lin(chi=1), "rel": "<=", "rhs": 2}},
    # 13 — is_connected ∧ has_cycle : girth ≤ 2·diam + 1
    {"name": "girth_le_diam", "lean_name": "SimpleGraph.girth_le_two_mul_diam_add_one",
     "source": "Mathlib", "properties": ["is_connected", "has_cycle"],
     "finite": ["girth", "diam"], "guards": [], "param": None,
     "conclusion": {"coeffs": _lin(girth=1, diam=-2), "rel": "<=", "rhs": 1}},
    # 14 — has_cycle : girth ≥ 3
    {"name": "girth_ge_three", "lean_name": "SimpleGraph.three_le_girth",
     "source": "Mathlib", "properties": ["has_cycle"], "finite": ["girth"],
     "guards": [], "param": None,
     "conclusion": {"coeffs": _lin(girth=1), "rel": ">=", "rhs": 3}},
    # 15 — is_connected ∧ nontrivial : min_deg ≥ 1
    {"name": "connected_min_deg", "lean_name": "SimpleGraph.Preconnected.minDegree_pos_of_nontrivial",
     "source": "Mathlib", "properties": ["is_connected", "nontrivial"], "finite": [],
     "guards": [], "param": None,
     "conclusion": {"coeffs": _lin(min_deg=1), "rel": ">=", "rhs": 1}},
    # 16a/b — is_regular(d) : max_deg = d, min_deg = d
    {"name": "regular_max", "lean_name": "SimpleGraph.IsRegularOfDegree.maxDegree_eq",
     "source": "Mathlib", "properties": ["is_regular"], "finite": [], "guards": [], "param": "d",
     "conclusion": {"coeffs": _lin(max_deg=1), "rel": "=", "rhs": "d"}},
    {"name": "regular_min", "lean_name": "SimpleGraph.IsRegularOfDegree.minDegree_eq",
     "source": "Mathlib", "properties": ["is_regular"], "finite": [], "guards": [], "param": "d",
     "conclusion": {"coeffs": _lin(min_deg=1), "rel": "=", "rhs": "d"}},
    # 17 — is_k_edge_connected(k) : min_deg ≥ k
    {"name": "edge_conn_min_deg", "lean_name": "PolyForge.Graph.isEdgeConnected_le_minDegree",
     "source": "GraphLemmas", "properties": ["is_k_edge_connected"], "finite": [],
     "guards": [], "param": "k",
     "conclusion": {"coeffs": _lin(min_deg=1), "rel": ">=", "rhs": "k"}},
    # 18 — is_connected ∧ nontrivial : diam ≥ 1   (v1.1.1, GraphLemmas)
    {"name": "diam_ge_one", "lean_name": "PolyForge.Graph.diam_ge_one_int",
     "source": "GraphLemmas", "properties": ["is_connected", "nontrivial"], "finite": ["diam"],
     "guards": [], "param": None,
     "conclusion": {"coeffs": _lin(diam=1), "rel": ">=", "rhs": 1}},
    # 19 — is_connected ∧ nontrivial : radius ≥ 1   (v1.1.1, GraphLemmas)
    {"name": "radius_ge_one", "lean_name": "PolyForge.Graph.radius_ge_one_int",
     "source": "GraphLemmas", "properties": ["is_connected", "nontrivial"], "finite": ["radius"],
     "guards": [], "param": None,
     "conclusion": {"coeffs": _lin(radius=1), "rel": ">=", "rhs": 1}},
    # 20 — is_connected : m ≥ n − 1   (v1.1.1, GraphLemmas)
    {"name": "connected_edges", "lean_name": "PolyForge.Graph.connected_edges_int",
     "source": "GraphLemmas", "properties": ["is_connected"], "finite": [],
     "guards": [], "param": None,
     "conclusion": {"coeffs": _lin(m=1, n=-1), "rel": ">=", "rhs": -1}},
    # 21 — n ≥ 1  (graphs assumed nonempty, v1.1.2 §I)
    {"name": "n_ge_one", "lean_name": "PolyForge.Graph.card_ge_one_int",
     "source": "GraphLemmas", "properties": [], "finite": [], "guards": [], "param": None,
     "conclusion": {"coeffs": _lin(n=1), "rel": ">=", "rhs": 1}},
    # 22 — alpha ≤ n  (v1.1.2 §II, GraphLemmas)
    {"name": "alpha_le_n", "lean_name": "PolyForge.Graph.alpha_le_card_int",
     "source": "GraphLemmas", "properties": [], "finite": [], "guards": [], "param": None,
     "conclusion": {"coeffs": _lin(alpha=1, n=-1), "rel": "<=", "rhs": 0}},
    # 23 — omega ≤ n  (v1.1.2 §II, Mathlib cliqueNum_le_natCard)
    {"name": "omega_le_n", "lean_name": "PolyForge.Graph.omega_le_card_int",
     "source": "GraphLemmas", "properties": [], "finite": [], "guards": [], "param": None,
     "conclusion": {"coeffs": _lin(omega=1, n=-1), "rel": "<=", "rhs": 0}},
    # 24 — tau ≤ m  (v1.1.2 §II, Mathlib vertexCoverNum_le_encard_edgeSet)
    {"name": "tau_le_m", "lean_name": "PolyForge.Graph.tau_le_edges_int",
     "source": "GraphLemmas", "properties": [], "finite": [], "guards": [], "param": None,
     "conclusion": {"coeffs": _lin(tau=1, m=-1), "rel": "<=", "rhs": 0}},
    # 25 — is_connected ∧ has_cycle : m ≥ n  (v1.1.2 §II, GraphLemmas)
    {"name": "conn_cycle_edges", "lean_name": "PolyForge.Graph.conn_cycle_edges_ge_card_int",
     "source": "GraphLemmas", "properties": ["is_connected", "has_cycle"], "finite": [],
     "guards": [], "param": None,
     "conclusion": {"coeffs": _lin(m=1, n=-1), "rel": ">=", "rhs": 0}},
]

INVENTORY_BY_NAME = {e["name"]: e for e in INVENTORY}


# ── numerical verification against a pool graph (checkpoint 1) ────────────────
def properties_of(g: dict) -> dict:
    """Derive the property flags of a pool graph dict (from graph_pool.json)."""
    n = g["n"]
    return {
        "is_connected": g["connected"],
        "is_tree": g["tree"],
        "is_acyclic": g["acyclic"],
        "is_bipartite": g["bipartite"],
        "not_bipartite": not g["bipartite"],
        "has_cycle": not g["acyclic"],
        "is_regular": g["regular"],
        "is_k_edge_connected": True,              # holds for k = edge_connectivity
        "nontrivial": n >= 2,
    }


def _values_of(g: dict) -> dict:
    return {
        "n": g["n"], "m": g["m"], "max_deg": g["max_degree"], "min_deg": g["min_degree"],
        "chi": g["chromatic_number"], "omega": g["clique_number"],
        "alpha": g["independence_number"], "tau": g["vertex_cover_number"],
        "diam": g["diameter"], "radius": g["radius"], "girth": g["girth"],
    }


def _holds(coeffs: dict, rel: str, rhs, vals: dict) -> bool:
    lhs = sum(Fraction(c) * Fraction(vals[v]) for v, c in coeffs.items())
    rhs = Fraction(rhs)
    if rel == "=":
        return lhs == rhs
    if rel == ">=":
        return lhs >= rhs
    if rel == "<=":
        return lhs <= rhs
    raise ValueError(rel)


def entry_applicable(entry: dict, g: dict) -> bool:
    props = properties_of(g)
    vals = _values_of(g)
    if not all(props.get(p, False) for p in entry["properties"]):
        return False
    for v in entry["finite"]:
        if vals[v] is None:                       # ⊤ : not finite here
            return False
    for guard in entry["guards"]:
        if not _holds(guard["coeffs"], guard["rel"], guard["rhs"], vals):
            return False
    return True


def _param_value(entry: dict, g: dict):
    if entry["param"] == "d":
        return g["regular_degree"]
    if entry["param"] == "k":
        return g["edge_connectivity"]
    return None


def entry_holds(entry: dict, g: dict) -> bool:
    vals = _values_of(g)
    concl = entry["conclusion"]
    rhs = concl["rhs"]
    if isinstance(rhs, str):                        # parametric rhs (d or k)
        rhs = _param_value(entry, g)
    return _holds(concl["coeffs"], concl["rel"], rhs, vals)


def verify_against_pool(pool: list) -> list:
    """Return a list of (entry_name, atlas_index) failures (empty = all hold)."""
    fails = []
    for g in pool:
        for entry in INVENTORY:
            if entry_applicable(entry, g) and not entry_holds(entry, g):
                fails.append((entry["name"], g.get("atlas_index")))
    return fails


if __name__ == "__main__":
    import json
    from pathlib import Path
    pool = json.load(open(Path(__file__).resolve().parent / "data" / "graph_pool.json"))["graphs"]
    pool = [g for g in pool if g["n"] >= 1]       # v1.1.2 §I: graphs assumed nonempty
    fails = verify_against_pool(pool)
    print(f"graphs (n>=1): {len(pool)}   inventory entries: {len(INVENTORY)}   failures: {len(fails)}")
    for f in fails[:20]:
        print("  FAIL", f)
