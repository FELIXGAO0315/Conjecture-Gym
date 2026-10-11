"""Graph-domain deduction configuration for the generic engine (PolyForge v1.1).

Supplies the engine with:
  * the variable set (ALL_VARS / PROP_VARS / NONNEG_VARS),
  * the directed objectives, case-split specs (chi threshold 2/3), B&B variables,
  * a per-premise-set *active inventory* holder (INVENTORY / CONDITIONAL_THEOREMS
    / INVENTORY_BY_NAME), rebuilt from inventory.py for the properties of the
    current premise set — this module is what the domain hands to
    ``anvil.deducer.configure`` as its ``inventory``,
  * exact invariant evaluation of a dataset graph (for the soundness regression).

Finiteness (§I/§III): diam/radius are usable only when ``is_connected`` holds,
girth only when ``has_cycle`` holds — enforced by only activating entries whose
required properties are present and by restricting the variables the generator
samples/enumerates.
"""

from __future__ import annotations

from fractions import Fraction

from . import inventory as INV

# ── variables (all ℕ-valued, all ≥ 0) ─────────────────────────────────────────
VARS = list(INV.VARS)                 # 11 invariants
ALL_VARS = list(VARS)
PROP_VARS = list(VARS)
NONNEG_VARS = list(VARS)
AUX_VARS = []                         # graph domain has no auxiliary variables

# which property grants finiteness of a conditional variable
FINITENESS = dict(INV.FINITENESS)     # diam/radius→is_connected, girth→has_cycle

# ── directed objectives explored every round ─────────────────────────────────
def _base_directions():
    dirs = []
    for v in VARS:
        dirs.append({v: 1})
        dirs.append({v: -1})
    return dirs


BASE_DIRECTIONS = _base_directions()

# ── case splits: "is bipartite?" as a chi threshold 2/3 split (§III.2) ─────────
# (label, coeff-dict, thresholds): split is ``expr >= c`` vs ``expr <= c-1``.
SPLIT_SPECS = [("chi", {"chi": 1}, [3])]

# ── branch-and-bound split variables ──────────────────────────────────────────
BNB_VARS = list(VARS)

# ── active inventory holder (rebuilt per premise set) ─────────────────────────
INVENTORY: list = []
CONDITIONAL_THEOREMS: list = []
INVENTORY_BY_NAME: dict = {}


def _entry_to_fact(entry: dict, param_value=None) -> dict:
    """An inventory entry's conclusion as a {name, lean_name, kind, conclusion}
    record for the deducer (``conclusion`` = {coeffs, rel, rhs})."""
    concl = entry["conclusion"]
    rhs = concl["rhs"]
    if isinstance(rhs, str):                       # parametric (d or k)
        rhs = param_value
    rel = concl["rel"]
    kind = "equality" if rel == "=" else "inequality"
    return {"name": entry["name"], "lean_name": entry["lean_name"], "kind": kind,
            "conclusion": {"coeffs": dict(concl["coeffs"]), "rel": rel, "rhs": int(rhs)}}


def set_active_inventory(properties: set, params: dict):
    """Rebuild the active inventory for a premise set.

    ``properties`` is the (implication-closed) set of property names present in
    the premises; ``params`` maps a parametric property name ("is_regular" /
    "is_k_edge_connected") to its integer parameter (d / k).  An entry is active
    iff all its required properties are present.  Numeric-guarded entries (n ≥ 1)
    become conditional theorems; everything else is an unconditional fact.  The
    bipartite/not_bipartite chi facts are added here too (§II.3)."""
    global INVENTORY, CONDITIONAL_THEOREMS, INVENTORY_BY_NAME
    inv, cond = [], []
    # v1.1.2 §I: graphs are assumed nonempty ([Nonempty V]), so every former
    # "n ≥ 1" guard is always satisfied — such entries are now UNCONDITIONAL and
    # their Lean wrappers use the nonempty-unconditional (…_int') forms.
    # edge_conn still needs Nontrivial V (n ≥ 2), supplied by the `nontrivial`
    # property (which `has_cycle` now implies, §II.2).
    _needs_nontrivial = {"edge_conn_min_deg"}
    for e in INV.INVENTORY:
        if not set(e["properties"]).issubset(properties):
            continue
        if e["name"] in _needs_nontrivial and "nontrivial" not in properties:
            continue
        pv = params.get(e["properties"][0]) if (e["param"] and e["properties"]) else None
        rec = _entry_to_fact(e, pv)
        inv.append(rec)                            # unconditional (n ≥ 1 always holds)
    # bipartite / not_bipartite → numeric chi fact (§II.3)
    if "is_bipartite" in properties:
        inv.append({"name": "bipartite_chi", "lean_name": "PolyForge.Graph.bipartite_chi_int",
                    "kind": "inequality",
                    "conclusion": {"coeffs": {"chi": 1}, "rel": "<=", "rhs": 2}})
    if "not_bipartite" in properties:
        inv.append({"name": "not_bipartite_chi", "lean_name": "PolyForge.Graph.not_bipartite_chi_int",
                    "kind": "inequality",
                    "conclusion": {"coeffs": {"chi": 1}, "rel": ">=", "rhs": 3}})
    # non-negativity of every variable (so the engine can use x ≥ 0)
    for v in NONNEG_VARS:
        inv.append({"name": f"nonneg_{v}", "lean_name": None, "kind": "inequality",
                    "conclusion": {"coeffs": {v: 1}, "rel": ">=", "rhs": 0}})
    INVENTORY = inv
    CONDITIONAL_THEOREMS = cond
    INVENTORY_BY_NAME = {e["name"]: e for e in (inv + cond)}


# ── exact invariant evaluation of a dataset graph (soundness) ─────────────────
def vars_from_graph(g: dict) -> dict:
    """Map a graph_pool.json entry to the exact variable valuation.  A ⊤ (null)
    invariant (disconnected diam/radius, acyclic girth) is returned as None; the
    soundness check only uses graphs whose premises make every used variable
    finite, so such a value is never compared."""
    def val(x):
        return None if x is None else Fraction(int(x))
    return {
        "n": val(g["n"]), "m": val(g["m"]),
        "max_deg": val(g["max_degree"]), "min_deg": val(g["min_degree"]),
        "chi": val(g["chromatic_number"]), "omega": val(g["clique_number"]),
        "alpha": val(g["independence_number"]), "tau": val(g["vertex_cover_number"]),
        "diam": val(g["diameter"]), "radius": val(g["radius"]), "girth": val(g["girth"]),
    }
