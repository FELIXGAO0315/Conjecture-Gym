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
VARS = ["n", "m", "max_deg", "min_deg", "chi", "omega", "alpha", "tau", "nu",
        "gamma", "kappa",
        "diam", "radius", "girth", "s2"]      # s2 = Σ deg²  (B §P1, Cauchy-Schwarz)
# nu    = matching number (max-cardinality matching, #edges).  v2.1 §M.
# gamma = domination number (min dominating set size).         v2.2 §D.
# kappa = vertex connectivity (κ; 0 if disconnected, n−1 if complete).  v2.2 §K.
# All always finite; each backed by self-proved GraphLemmas defs + ℤ bounds.

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
    # 26 — omega ≤ max_deg + 1  (v1.2.1 §VI, GraphLemmas) — linear
    {"name": "omega_le_maxdeg", "lean_name": "PolyForge.Graph.omega_le_maxdeg_add_one_int",
     "source": "GraphLemmas", "properties": [], "finite": [], "guards": [], "param": None,
     "conclusion": {"coeffs": _lin(omega=1, max_deg=-1), "rel": "<=", "rhs": 1}},
    # 27 — is_connected : diam ≤ n − 1  (v1.2.2 §IV)
    {"name": "diam_le_card_sub_one", "lean_name": "PolyForge.Graph.diam_le_card_sub_one_int",
     "source": "GraphLemmas", "properties": ["is_connected"], "finite": ["diam"],
     "guards": [], "param": None,
     "conclusion": {"coeffs": _lin(diam=1, n=-1), "rel": "<=", "rhs": -1}},
    # 28 — has_cycle : girth ≤ n  (v1.2.2 §IV)
    {"name": "girth_le_card", "lean_name": "PolyForge.Graph.girth_le_card_int",
     "source": "GraphLemmas", "properties": ["has_cycle"], "finite": ["girth"],
     "guards": [], "param": None,
     "conclusion": {"coeffs": _lin(girth=1, n=-1), "rel": "<=", "rhs": 0}},
    # 29 — has_cycle : m ≥ 3  (v1.2.2 §IV)
    {"name": "cycle_three_le_edges", "lean_name": "PolyForge.Graph.three_le_edges_int",
     "source": "GraphLemmas", "properties": ["has_cycle"], "finite": [], "guards": [], "param": None,
     "conclusion": {"coeffs": _lin(m=1), "rel": ">=", "rhs": 3}},
    # 30 — has_cycle : n ≥ 3  (v1.2.2 §IV.5)
    {"name": "cycle_three_le_card", "lean_name": "PolyForge.Graph.three_le_card_of_cycle_int",
     "source": "GraphLemmas", "properties": ["has_cycle"], "finite": [], "guards": [], "param": None,
     "conclusion": {"coeffs": _lin(n=1), "rel": ">=", "rhs": 3}},
    # ── v2.1 §M: matching number ν (self-proved matchingNumber + ℤ bounds) ──────
    # 31 — 2ν ≤ n   (a matching saturates 2ν distinct vertices)
    {"name": "nu_bound_card", "lean_name": "PolyForge.Graph.two_mul_matchingNumber_le_card_int",
     "source": "GraphLemmas", "properties": [], "finite": [], "guards": [], "param": None,
     "conclusion": {"coeffs": _lin(nu=2, n=-1), "rel": "<=", "rhs": 0}},
    # 32 — ν ≤ m   (matching edges ⊆ edges)
    {"name": "nu_le_m", "lean_name": "PolyForge.Graph.matchingNumber_le_edges_int",
     "source": "GraphLemmas", "properties": [], "finite": [], "guards": [], "param": None,
     "conclusion": {"coeffs": _lin(nu=1, m=-1), "rel": "<=", "rhs": 0}},
    # 33 — ν ≤ τ   (weak LP duality: each matching edge needs a distinct cover vertex)
    {"name": "nu_le_tau", "lean_name": "PolyForge.Graph.matchingNumber_le_vertexCoverNum_int",
     "source": "GraphLemmas", "properties": [], "finite": [], "guards": [], "param": None,
     "conclusion": {"coeffs": _lin(nu=1, tau=-1), "rel": "<=", "rhs": 0}},
    # ── v2.2 §D: domination number γ (self-proved dominationNumber + ℤ bounds) ──
    # 34 — γ ≤ n   (the whole vertex set dominates)
    {"name": "gamma_le_n", "lean_name": "PolyForge.Graph.dominationNumber_le_card_int",
     "source": "GraphLemmas", "properties": [], "finite": [], "guards": [], "param": None,
     "conclusion": {"coeffs": _lin(gamma=1, n=-1), "rel": "<=", "rhs": 0}},
    # 35 — γ ≥ 1   (nonempty graph needs at least one dominator)
    {"name": "gamma_ge_one", "lean_name": "PolyForge.Graph.one_le_dominationNumber_int",
     "source": "GraphLemmas", "properties": [], "finite": [], "guards": [], "param": None,
     "conclusion": {"coeffs": _lin(gamma=1), "rel": ">=", "rhs": 1}},
    # 36 — γ ≤ α   (a maximum independent set is dominating)
    {"name": "gamma_le_alpha", "lean_name": "PolyForge.Graph.dominationNumber_le_indepNum_int",
     "source": "GraphLemmas", "properties": [], "finite": [], "guards": [], "param": None,
     "conclusion": {"coeffs": _lin(gamma=1, alpha=-1), "rel": "<=", "rhs": 0}},
    # ── v2.2 §K: vertex connectivity κ (self-proved vertexConnectivity + ℤ bounds) ─
    # 37 — κ ≤ n − 1
    {"name": "kappa_le_n_sub_one", "lean_name": "PolyForge.Graph.vertexConnectivity_le_card_sub_one_int",
     "source": "GraphLemmas", "properties": [], "finite": [], "guards": [], "param": None,
     "conclusion": {"coeffs": _lin(kappa=1, n=-1), "rel": "<=", "rhs": -1}},
    # 38 — κ ≤ δ   (Whitney: remove a min-degree vertex's neighborhood)
    {"name": "kappa_le_mindeg", "lean_name": "PolyForge.Graph.vertexConnectivity_le_minDegree_int",
     "source": "GraphLemmas", "properties": [], "finite": [], "guards": [], "param": None,
     "conclusion": {"coeffs": _lin(kappa=1, min_deg=-1), "rel": "<=", "rhs": 0}},
    # 39 — is_connected ∧ nontrivial : κ ≥ 1  (gives κ a LOWER bound → generativity)
    {"name": "conn_kappa_ge_one", "lean_name": "PolyForge.Graph.one_le_vertexConnectivity_int",
     "source": "GraphLemmas", "properties": ["is_connected", "nontrivial"], "finite": [],
     "guards": [], "param": None,
     "conclusion": {"coeffs": _lin(kappa=1), "rel": ">=", "rhs": 1}},
]

INVENTORY_BY_NAME = {e["name"]: e for e in INVENTORY}

# ── v1.2 §II/§III: product (handshake / edge-count) facts ─────────────────────
# PolyForge v1.2 stage 2a introduces facts that pass through a *product* of two
# invariants.  Each product is carried by a proof-only auxiliary variable (never
# part of a proposition statement, like the hex domain's W_tail / J_tail):
#
#     P_n_mindeg = n · min_deg      P_n_maxdeg = n · max_deg      N2 = n · n
#
# A PRODUCT_INVENTORY entry is a linear (in)equality over the invariant variables
# AND these product variables.  The engine connects a product variable to its
# factors via McCormick envelope inequalities generated per context (the product
# inference step, §III).  Each entry carries the same fields as an INVENTORY entry
# plus nothing extra; the ℤ wrapper is a self-proved GraphLemmas lemma.
PRODUCT_VARS = {
    "P_n_mindeg": ("n", "min_deg"),
    "P_n_maxdeg": ("n", "max_deg"),
    "N2": ("n", "n"),
    "P_alpha_chi": ("alpha", "chi"),           # v1.2.1 §VI.1
    "M2": ("m", "m"),                          # B §P1: m²  (for Cauchy-Schwarz)
    "P_n_s2": ("n", "s2"),                     # B §P1: n·Σdeg²
}

PRODUCT_INVENTORY = [
    # P1 — n·min_deg ≤ 2m        (handshake lower:  P_n_mindeg − 2m ≤ 0)
    {"name": "handshake_min", "lean_name": "PolyForge.Graph.handshake_min_int",
     "source": "GraphLemmas", "properties": [], "finite": [], "guards": [], "param": None,
     "conclusion": {"coeffs": _lin(P_n_mindeg=1, m=-2), "rel": "<=", "rhs": 0}},
    # P2 — 2m ≤ n·max_deg        (handshake upper:  2m − P_n_maxdeg ≤ 0)
    {"name": "handshake_max", "lean_name": "PolyForge.Graph.handshake_max_int",
     "source": "GraphLemmas", "properties": [], "finite": [], "guards": [], "param": None,
     "conclusion": {"coeffs": _lin(m=2, P_n_maxdeg=-1), "rel": "<=", "rhs": 0}},
    # P4 — 2m ≤ n² − n           (edge bound:  2m + n − N2 ≤ 0)
    {"name": "edge_card_bound", "lean_name": "PolyForge.Graph.two_mul_edges_le_card_sq_sub_card_int",
     "source": "GraphLemmas", "properties": [], "finite": [], "guards": [], "param": None,
     "conclusion": {"coeffs": _lin(m=2, n=1, N2=-1), "rel": "<=", "rhs": 0}},
    # P5 — is_bipartite : 4m ≤ n²  (bipartite edge bound:  4m − N2 ≤ 0)
    {"name": "bipartite_edges", "lean_name": "PolyForge.Graph.bipartite_four_mul_edges_int",
     "source": "GraphLemmas", "properties": ["is_bipartite"], "finite": [], "guards": [], "param": None,
     "conclusion": {"coeffs": _lin(m=4, N2=-1), "rel": "<=", "rhs": 0}},
    # P6 — n ≤ alpha·chi  (v1.2.1 §VI.1:  n − P_alpha_chi ≤ 0)
    {"name": "card_le_alpha_chi", "lean_name": "PolyForge.Graph.card_le_alpha_chi_int",
     "source": "GraphLemmas", "properties": [], "finite": [], "guards": [], "param": None,
     "conclusion": {"coeffs": _lin(n=1, P_alpha_chi=-1), "rel": "<=", "rhs": 0}},
    # P7 — Cauchy-Schwarz on degrees (B §P1):  4·m² ≤ n·Σdeg²   (4·M2 − P_n_s2 ≤ 0)
    {"name": "deg_cauchy", "lean_name": "PolyForge.Graph.deg_cauchy_int",
     "source": "GraphLemmas", "properties": [], "finite": [], "guards": [], "param": None,
     "conclusion": {"coeffs": _lin(M2=4, P_n_s2=-1), "rel": "<=", "rhs": 0}},
]
PRODUCT_INVENTORY_BY_NAME = {e["name"]: e for e in PRODUCT_INVENTORY}

# ── v1.2.1 §VI.2: Turán-type conditional theorems (hypothesis omega ≤ r) ───────
# omega ≤ r ⟹ CliqueFree(r+1) ⟹ 2r·m ≤ (r−1)·n² (= (r−1)·N2).  r = 2 is Mantel
# (4m ≤ n²).  Conditional on a numeric clique-number cap; triggers under an
# explicit omega bound or the omega-threshold case split (§VI.6).
TURAN = [
    {"name": f"turan_r{r}", "lean_name": f"PolyForge.Graph.turan_r{r}_int",
     "source": "GraphLemmas", "properties": [], "param": None,
     "hypothesis": {"coeffs": _lin(omega=1), "rel": "<=", "rhs": r},
     "conclusion": {"coeffs": _lin(m=2 * r, N2=-(r - 1)), "rel": "<=", "rhs": 0}}
    for r in (2, 3, 4, 5, 6)
]
TURAN_BY_NAME = {e["name"]: e for e in TURAN}

# ── v1.2.2 §II: complete graph (chi ≥ n ⟺ chi = n) ⟹ alpha ≤ 1 ────────────────
# A conditional theorem (numeric hypothesis chi ≥ n).  Lets the engine see that a
# premise set forcing chi = n (e.g. C115's tau ≤ alpha ∧ chi ≥ n) only admits the
# complete graph, hence alpha ≤ 1 and (with Gallai) a degenerate small graph.
COMPLETE_INDEP = {
    "name": "complete_indep", "lean_name": "PolyForge.Graph.complete_indep_le_one_int",
    "source": "GraphLemmas", "properties": [], "param": None,
    "hypothesis": {"coeffs": _lin(chi=1, n=-1), "rel": ">=", "rhs": 0},
    "conclusion": {"coeffs": _lin(alpha=1), "rel": "<=", "rhs": 1},
}
CONDITIONALS = list(TURAN) + [COMPLETE_INDEP]

# P3 — is_regular(d) : 2m = d·n is LINEAR (d a constant), so it is an ordinary
# (parametric) INVENTORY-style entry rather than a product entry.  Its coefficient
# on n is the parameter d; the active-inventory builder substitutes d.
REGULAR_EDGES = {
    "name": "regular_edges", "lean_name": "PolyForge.Graph.regular_edges_int",
    "source": "GraphLemmas", "properties": ["is_regular"], "finite": [], "guards": [], "param": "d",
    # conclusion built per premise set (2m − d·n = 0) by set_active_inventory
}


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
    vals = {
        "n": g["n"], "m": g["m"], "max_deg": g["max_degree"], "min_deg": g["min_degree"],
        "chi": g["chromatic_number"], "omega": g["clique_number"],
        "alpha": g["independence_number"], "tau": g["vertex_cover_number"],
        "diam": g["diameter"], "radius": g["radius"], "girth": g["girth"],
        "s2": g["sum_deg_sq"],                 # B §P1: Σ deg²
        "nu": g["matching_number"],            # v2.1 §M: matching number
        "gamma": g["domination_number"],       # v2.2 §D: domination number
        "kappa": g["vertex_connectivity"],     # v2.2 §K: vertex connectivity
    }
    # v1.2: exact product-variable values (real products; §VI.3 regression)
    for pv, (a, b) in PRODUCT_VARS.items():
        va, vb = vals.get(a), vals.get(b)
        vals[pv] = None if (va is None or vb is None) else va * vb
    return vals


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


def _regular_edges_entry(g: dict):
    """Build the concrete 2m = d·n fact for a regular graph (d = its degree)."""
    d = g["regular_degree"]
    if d is None:
        return None
    return {**REGULAR_EDGES,
            "conclusion": {"coeffs": {"m": Fraction(2), "n": Fraction(-d)}, "rel": "=", "rhs": 0}}


def verify_against_pool(pool: list) -> list:
    """Return a list of (entry_name, atlas_index) failures (empty = all hold).
    Covers the linear INVENTORY, the product PRODUCT_INVENTORY, and the parametric
    regular-edges fact — all checked with exact real values (products included)."""
    fails = []
    for g in pool:
        entries = list(INVENTORY) + list(PRODUCT_INVENTORY)
        if g.get("regular"):
            re = _regular_edges_entry(g)
            if re is not None:
                entries.append(re)
        for entry in entries:
            if entry_applicable(entry, g) and not entry_holds(entry, g):
                fails.append((entry["name"], g.get("atlas_index")))
        # v1.2.1 §VI.2 / v1.2.2 §II: conditional theorems — when the hypothesis
        # holds the conclusion must hold (Turán edge bound; complete-graph alpha ≤ 1).
        vals = _values_of(g)
        for e in CONDITIONALS:
            h = e["hypothesis"]
            if _holds(h["coeffs"], h["rel"], h["rhs"], vals):
                c = e["conclusion"]
                if not _holds(c["coeffs"], c["rel"], c["rhs"], vals):
                    fails.append((e["name"], g.get("atlas_index")))
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
