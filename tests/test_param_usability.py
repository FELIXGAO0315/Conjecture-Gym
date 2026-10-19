#!/usr/bin/env python3
"""v1.4.6 §3.2: regression tests for parameter-aware property usability in OUR code,
from the v1.4.5 counterexamples (is_regular(2) vs is_regular(3); k-edge-connectivity).
These exercise generator.props_dischargeable and the generator's _premises_imply /
_avail_for (which now route through PolyForge.trust.props.dischargeable).

Run: python tests/test_param_usability.py
"""
import sys
sys.path.insert(0, "/home/felix_gao/Conjecture-Gym")
from PolyForge.domains.graph.domain import GraphDomain
from PolyForge.anvil import deducer as D
from PolyForge.domains.graph import generator as G
dom = GraphDomain(); D.configure(dom)


def P(name, param=None):
    return {"name": name} if param is None else {"name": name, "param": param}


def run():
    pd = G.props_dischargeable
    # is_regular: exact parameter; 2-regular does NOT discharge 3-regular (the v1.4.5 bug)
    assert pd([P("is_regular", 3)], [P("is_regular", 2)]) is False
    assert pd([P("is_regular", 2)], [P("is_regular", 2)]) is True
    assert pd([P("is_regular", 2)], [P("is_regular", 3)]) is False
    # is_k_edge_connected: monotone; 2-edge-conn discharges 1-edge-conn, not vice versa
    assert pd([P("is_k_edge_connected", 1)], [P("is_k_edge_connected", 2)]) is True
    assert pd([P("is_k_edge_connected", 2)], [P("is_k_edge_connected", 1)]) is False
    # non-parametric lattice still works (is_tree => is_connected, is_acyclic)
    assert pd([P("is_connected")], [P("is_tree")]) is True
    assert pd([P("is_acyclic")], [P("is_tree")]) is True
    # mixed: a regular-degree mismatch is not rescued by the lattice
    assert pd([P("is_regular", 3)], [P("is_tree")]) is False

    # end-to-end through the generator's _premises_imply on record-style views:
    # A = is_regular(2), B = is_regular(3), identical numeric -> A must NOT imply B.
    def view(props):
        pset = G.property_closure({p["name"] for p in props})
        params = {p["name"]: p.get("param") for p in props if "param" in p}
        return {"props": props, "pset": pset, "params": params, "numeric": []}
    A, B = view([P("is_regular", 2)]), view([P("is_regular", 3)])
    G.clear_impl_cache()
    assert G._premises_imply(A, B) is False, "is_regular(2) must not imply is_regular(3)"
    assert G._premises_imply(A, view([P("is_regular", 2)])) is True
    assert G._premises_imply(view([P("is_k_edge_connected", 2)]),
                             view([P("is_k_edge_connected", 1)])) is True
    assert G._premises_imply(view([P("is_k_edge_connected", 1)]),
                             view([P("is_k_edge_connected", 2)])) is False
    print("test_param_usability: PASS (is_regular exact, k-edge-conn monotone, lattice intact)")


if __name__ == "__main__":
    run()
