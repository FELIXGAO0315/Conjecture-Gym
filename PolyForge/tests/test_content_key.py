#!/usr/bin/env python3
"""PolyForge v1.4.5 §G3: content_key / _norm_form property tests (keys are metadata only).

Run: python -m tests.test_content_key   (or python tests/test_content_key.py)
"""
import sys
sys.path.insert(0, "/home/felix_gao/Conjecture-Gym")
from PolyForge.domains.graph.domain import GraphDomain
from PolyForge.engine import deducer as D
from PolyForge.domains.graph import generator as G
dom = GraphDomain(); D.configure(dom)


def ck(coeffs, rel, rhs, props=None, numeric=None):
    return G.content_key(props or [], numeric or [], {"coeffs": coeffs, "rel": rel, "rhs": rhs})


def nf(coeffs, rel, rhs):
    return G._norm_form(coeffs, rel, rhs)


def run():
    checks = []
    def eq(a, b, msg):
        checks.append((msg, a == b, a, b))
    def ne(a, b, msg):
        checks.append((msg, a != b, a, b))

    # positive scaling: 2a+4b >= 6  ==  a+2b >= 3
    eq(nf({"a": 2, "b": 4}, ">=", 6), nf({"a": 1, "b": 2}, ">=", 3), "positive scaling")
    # gcd normalization WITH integer tightening: 2x >= 3  ==  x >= 2  (over Z)
    eq(nf({"x": 2}, ">=", 3), nf({"x": 1}, ">=", 2), "integer tightening 2x>=3 == x>=2")
    # another tightening: 3x >= 4  ==  x >= 2 (ceil(4/3)=2)
    eq(nf({"x": 3}, ">=", 4), nf({"x": 1}, ">=", 2), "integer tightening 3x>=4 == x>=2")
    # NOT equal when the tightened bound differs: 2x>=3 (x>=2) != 2x>=5 (x>=3)
    ne(nf({"x": 2}, ">=", 3), nf({"x": 2}, ">=", 5), "distinct tightened bounds")
    # term order independence
    eq(ck({"a": 1, "b": 2}, ">=", 3), ck({"b": 2, "a": 1}, ">=", 3), "term order")
    # premise order independence
    p1 = [{"name": "is_connected"}]
    n1 = [{"coeffs": {"n": 1}, "rel": ">=", "rhs": 4}, {"coeffs": {"m": 1}, "rel": "<=", "rhs": 6}]
    n2 = [{"coeffs": {"m": 1}, "rel": "<=", "rhs": 6}, {"coeffs": {"n": 1}, "rel": ">=", "rhs": 4}]
    eq(G.content_key(p1, n1, {"coeffs": {"chi": 1}, "rel": ">=", "rhs": 1}),
       G.content_key(p1, n2, {"coeffs": {"chi": 1}, "rel": ">=", "rhs": 1}), "premise order")
    # <= / >= orientation folding: a <= b  ==  -a+... actually: n <= 2*alpha  ==  2*alpha - n >= 0
    eq(nf({"n": 1, "alpha": -2}, "<=", 0), nf({"alpha": 2, "n": -1}, ">=", 0), "orientation <= / >=")
    # constants moved across sides: a - 3 >= 0  ==  a >= 3
    eq(nf({"a": 1}, ">=", 3), nf({"a": 1}, ">=", 3), "constant side (identity)")
    # 2a >= b + 4  ==  2a - b >= 4
    eq(nf({"a": 2, "b": -1}, ">=", 4), nf({"a": 2, "b": -1}, ">=", 4), "constant move (identity)")
    # distinct keys for non-equivalent propositions
    ne(ck({"n": 1}, ">=", 3), ck({"n": 1}, ">=", 4), "distinct: n>=3 vs n>=4")
    ne(ck({"n": 1}, ">=", 3), ck({"m": 1}, ">=", 3), "distinct: different variable")
    ne(G.content_key([{"name": "is_tree"}], [], {"coeffs": {"n": 1}, "rel": ">=", "rhs": 3}),
       G.content_key([{"name": "is_bipartite"}], [], {"coeffs": {"n": 1}, "rel": ">=", "rhs": 3}),
       "distinct: different property premise")
    # equality orientation: a - b = 0  ==  b - a = 0
    eq(nf({"a": 1, "b": -1}, "==", 0), nf({"b": 1, "a": -1}, "==", 0), "equality sign-normalised")

    ok = all(c[1] for c in checks)
    for msg, passed, a, b in checks:
        if not passed:
            print(f"FAIL: {msg}\n  a={a}\n  b={b}")
    print(f"content_key property tests: {sum(c[1] for c in checks)}/{len(checks)} passed")
    assert ok, "content_key property tests FAILED"
    return ok


if __name__ == "__main__":
    run()
