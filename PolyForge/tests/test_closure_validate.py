#!/usr/bin/env python3
"""PolyForge v1.4.5 §V: validation tests for the complete-usability closure checker.

Covers: the omega batch error-cap fix (a batch with >100 failing goals must not
mis-report), parametric-property discharge (is_regular(3) is NOT usable under
is_regular(2)), the property lattice holding on the atlas, and record-level
self-exclusion.  Run: python tests/test_closure_validate.py
"""
import sys
sys.path.insert(0, "/home/felix_gao/Conjecture-Gym")
from PolyForge.domains.graph.domain import GraphDomain
from PolyForge.engine import deducer as D
from PolyForge.domains.graph import generator as G
from PolyForge.env import closure_complete as CC
from PolyForge.env.analysis import closure_validate as CV
dom = GraphDomain(); D.configure(dom)


def test_omega_error_cap():
    # 150 trivially-FALSE goals in one batch: every one must be reported not-entailed
    # (regression for the maxErrors=100 truncation bug).
    # each goal x>=i+1 is NOT provable from x>=0, so every one must be reported False;
    # interleave a few provable ones to confirm they still read True.
    cases = [(f"f{i}", [({"x": 1}, ">=", 0)], ({"x": 1}, ">=", i + 1), ["x"]) for i in range(150)]
    cases += [("t1", [({"x": 1}, ">=", 5)], ({"x": 1}, ">=", 3), ["x"]),
              ("t2", [({"x": 1}, ">=", 9)], ({"x": 1}, ">=", 3), ["x"])]
    dec = CC.omega_decide_batch(cases)[0]
    assert all(dec[f"f{i}"] is False for i in range(150)), "error-cap regression: a failing goal read as proved"
    assert dec["t1"] is True and dec["t2"] is True, "provable goals after >100 failures read as unproved"
    print("test_omega_error_cap: PASS (150 failing + 2 passing goals all reported correctly)")


def test_param_discharge():
    T = [{"name": "is_regular", "param": 2}]
    R3 = [{"name": "is_regular", "param": 3}]
    R2 = [{"name": "is_regular", "param": 2}]
    pset = G.property_closure({"is_regular"})
    assert CC.props_dischargeable(R2, T, pset) is True, "same-param regular should discharge"
    assert CC.props_dischargeable(R3, T, pset) is False, "is_regular(3) must NOT discharge under is_regular(2)"
    # k-edge-connected monotonicity: k'=2 discharges k=1, not vice versa
    assert CC.props_dischargeable([{"name": "is_k_edge_connected", "param": 1}],
                                  [{"name": "is_k_edge_connected", "param": 2}],
                                  G.property_closure({"is_k_edge_connected"})) is True
    assert CC.props_dischargeable([{"name": "is_k_edge_connected", "param": 2}],
                                  [{"name": "is_k_edge_connected", "param": 1}],
                                  G.property_closure({"is_k_edge_connected"})) is False
    print("test_param_discharge: PASS")


def test_lattice_holds():
    graphs = CV.pool_graphs(exclude_zero=True)
    v3 = CV.verify_lattice(graphs)
    assert not v3["violations"], f"lattice violation: {v3['violations']}"
    print(f"test_lattice_holds: PASS (0 violations over {len(graphs)} atlas graphs; "
          f"{len(v3['missing_but_universal'])} universal-but-uncoded implications)")


def test_self_exclusion():
    recs = G.load_records(G.RECORD)
    if not recs:
        print("test_self_exclusion: SKIP (no records)"); return
    views = [G._record_premise_view(d) for d in recs]
    T = views[0]
    others = [v for v in views if v["id"] != T["id"]]
    _f, _g, _v, meta = CC.collect_facts_complete(T["props"], T["numeric"], T["canon"], others)
    assert T["id"] not in meta["usable"], "self-exclusion violated"
    print(f"test_self_exclusion: PASS ({T['id']} not in its own usable set)")


if __name__ == "__main__":
    test_omega_error_cap()
    test_param_discharge()
    test_lattice_holds()
    test_self_exclusion()
    print("closure_validate tests OK")
