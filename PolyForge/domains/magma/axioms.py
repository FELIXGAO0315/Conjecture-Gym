"""Magma equational-law axiom library.

A magma law is an identity over the free magma (a type with one binary op `*`).
Each axiom here is given as an ORIENTED, terminating rewrite rule  lhs → rhs  (so a
set of them normalizes terms), used by the forward generator to derive consequences.

Term representation:  ('v', i)  variable i  |  ('op', t1, t2)  product t1 * t2
Axiom tuple:          (lhs, rhs, n_vars, name)
"""
from __future__ import annotations


def V(i): return ('v', i)
def Op(a, b): return ('op', a, b)


AXIOMS = {
    # (x*y)*z → x*(y*z)   right-associate (terminating)
    "assoc": (Op(Op(V(0), V(1)), V(2)), Op(V(0), Op(V(1), V(2))), 3, "assoc"),
    # x*x → x             idempotent
    "idem":  (Op(V(0), V(0)), V(0), 1, "idem"),
    # x*y → x             left projection
    "lproj": (Op(V(0), V(1)), V(0), 2, "lproj"),
    # x*y → y             right projection
    "rproj": (Op(V(0), V(1)), V(1), 2, "rproj"),
}


def get(names):
    """Resolve a list of axiom names to axiom tuples."""
    return [AXIOMS[n] for n in names]
