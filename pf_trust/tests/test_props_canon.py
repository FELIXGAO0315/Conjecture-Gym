import itertools
import random

import networkx as nx
import pytest

from pf_trust.canon import FALSE, TRUE, Lin, canon, content_key
from pf_trust.props import dischargeable, parse_prop

ATLAS = [g for g in nx.graph_atlas_g() if g.number_of_nodes() >= 1]


def has(g, prop):
    name, args = parse_prop(prop)
    if name == "is_regular":
        return all(d == args[0] for _, d in g.degree())
    if name == "is_k_edge_connected":
        if g.number_of_nodes() < 2 or not nx.is_connected(g):
            return False
        return nx.edge_connectivity(g) >= args[0]
    raise KeyError(name)


def identity(s):
    return set(s)


PROPS = [f"is_regular({d})" for d in range(5)] + [f"is_k_edge_connected({k})" for k in range(1, 4)]


def test_param_rules_sound_on_atlas():
    for need, have_p in itertools.product(PROPS, PROPS):
        if dischargeable([need], [have_p], identity):
            for g in ATLAS:
                if has(g, have_p):
                    assert has(g, need), (need, have_p, list(g.edges()))


def test_name_only_matching_is_unsound():
    # the v1.4.5 bug: is_regular(2) graph (triangle) violates is_regular(3)
    tri = nx.cycle_graph(3)
    assert has(tri, "is_regular(2)") and not has(tri, "is_regular(3)")
    assert not dischargeable(["is_regular(3)"], ["is_regular(2)"], identity)


def test_k_edge_monotone_and_lattice_untouched_by_params():
    assert dischargeable(["is_k_edge_connected(1)"], ["is_k_edge_connected(2)"], identity)
    assert not dischargeable(["is_k_edge_connected(2)"], ["is_k_edge_connected(1)"], identity)

    def closure(s):  # toy lattice: is_tree => is_connected
        return s | ({"is_connected"} if "is_tree" in s else set())

    assert dischargeable(["is_connected"], ["is_tree"], closure)
    assert not dischargeable(["is_regular(2)"], ["is_tree"], closure)
    assert not dischargeable(["unknown_p(3)"], ["unknown_p(4)"], identity)
    assert dischargeable(["unknown_p(3)"], ["unknown_p(3)"], identity)


# ---------------- canonical form ----------------

def holds(c, env):
    v = sum(k * env[x] for x, k in c.coefs.items()) + c.const
    return {">=": v >= 0, "<=": v <= 0, "==": v == 0}[c.op]


def holds_canon(cc, env):
    if cc == TRUE:
        return True
    if cc == FALSE:
        return False
    op, coefs, const = cc
    v = sum(k * env[x] for x, k in coefs) + const
    return v >= 0 if op == ">=" else v == 0


def test_tightening_examples():
    assert canon(Lin({"x": 2}, -3, ">=")) == (">=", (("x", 1),), -2)   # 2x>=3 -> x>=2
    assert canon(Lin({"x": 2}, 3, ">=")) == (">=", (("x", 1),), 1)     # 2x>=-3 -> x>=-1
    assert canon(Lin({"x": 2}, 1, "==")) == FALSE
    assert canon(Lin({"x": -2, "y": 4}, 6, "==")) == canon(Lin({"x": 1, "y": -2}, -3, "=="))
    assert canon(Lin({"x": 1}, -3, "<=")) == canon(Lin({"x": -1}, 3, ">="))
    assert canon(Lin({}, 0, ">=")) == TRUE


def test_canon_is_integer_equivalent_random():
    rnd = random.Random(0)
    grid = list(itertools.product(range(-4, 5), repeat=2))
    for _ in range(3000):
        c = Lin({"x": rnd.randint(-6, 6), "y": rnd.randint(-6, 6)},
                rnd.randint(-12, 12), rnd.choice([">=", "<=", "=="]))
        cc = canon(c)
        for x, y in grid:
            env = {"x": x, "y": y}
            assert holds(c, env) == holds_canon(cc, env), (c, cc, env)


def test_key_invariances():
    p = [Lin({"n": 2}, -4, ">="), Lin({"m": 1}, -1, ">=")]
    concl = Lin({"m": 3, "n": -3}, 6, ">=")
    k = content_key(["is_tree", "is_regular(2)"], p, concl)
    assert k == content_key(["is_regular( 2 )", "is_tree"], list(reversed(p)),
                            Lin({"n": 1, "m": -1}, -2, "<="))
    assert k == content_key(["is_tree", "is_regular(2)"], p + [Lin({}, 1, ">=")], concl)
    assert k != content_key(["is_tree", "is_regular(3)"], p, concl)
    assert k != content_key(["is_tree", "is_regular(2)"], p, Lin({"m": 1, "n": -1}, 1, ">="))


def test_is_k_edge_connected_rejects_malformed_arity():
    # v1.5 audit hardening: a malformed 2-arg form must NOT discharge a 1-arg need by
    # inspecting only the first argument.
    from pf_trust.props import dischargeable
    def closure(s):
        return set(s)
    # well-formed monotone case still works
    assert dischargeable(["is_k_edge_connected(3)"], ["is_k_edge_connected(5)"], closure) is True
    # malformed 2-arg available does NOT discharge a 1-arg need
    assert dischargeable(["is_k_edge_connected(3)"], ["is_k_edge_connected(5,9)"], closure) is False
    # malformed 2-arg need is not discharged by a 1-arg available either
    assert dischargeable(["is_k_edge_connected(3,1)"], ["is_k_edge_connected(5)"], closure) is False
