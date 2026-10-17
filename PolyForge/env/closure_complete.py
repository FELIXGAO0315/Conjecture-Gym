#!/usr/bin/env python3
"""PolyForge v1.4.3 §C: closure in the COMPLETE sense.

The production redundancy/closure engine (``_restricted_derive``) proves a goal from
the usable record conclusions + the restricted (linear) Inventory + the premises by
LP-directed linear combination plus BOUNDED integer rounding (``DEFAULT_MAX_ROUNDS``);
it is sound but not complete — the fact set shrinks as records are pruned, and the
bounded rounding does not compose.  This module replaces the bounded step by a
COMPLETE linear-integer decision: it collects exactly the input linear facts the
restricted criterion may use (premises, active restricted-Inventory facts incl. fired
conditionals, and the usable record conclusions — all linear over the base integer
invariants; the restricted view carries no product terms), and asks Lean ``omega``
(a complete decision procedure for linear integer arithmetic) whether they entail the
goal.  ``omega`` succeeding ⇒ entailed; ``omega`` reporting a counterexample ⇒ not
entailed (a genuine information loss, not a bounded-rounds artifact).
"""
import json, re, subprocess, sys
from fractions import Fraction
from math import gcd
from pathlib import Path

sys.path.insert(0, "/home/felix_gao/Conjecture-Gym")
from PolyForge.domains.graph.domain import GraphDomain
from PolyForge.anvil import deducer as D
from PolyForge.anvil.deducer import Context
from PolyForge.domains.graph import generator as G

dom = GraphDomain(); D.configure(dom)
_LEAN_DIR = Path("/home/felix_gao/Conjecture-Gym/PolyForge/domains/graph/lean")
_INPUT_RULES = {"premise", "inventory", "conditional", "assumption", "lemma", "product"}


def _lean_var(v):
    return "v_" + v


def collect_facts(props, numeric, canon, record_views, max_rounds=64):
    """Return ``(facts, goal, vars)``: the input linear facts usable under the restricted
    criterion for proposition (props, numeric, canon), the goal, and the variable set.
    Each fact/goal is ``(int_coeffs, rel, int_rhs)`` for ``coeffs·x REL rhs``.  Facts =
    premises + usable record conclusions + the active restricted-Inventory facts that the
    restricted saturation makes available (unconditional + fired conditionals)."""
    pset = G.property_closure({p["name"] for p in props})
    params = {p["name"]: p.get("param") for p in props if "param" in p}
    S = {"id": None, "props": props, "pset": pset, "params": params,
         "numeric": numeric, "canon": canon, "disp": canon}
    D.set_lemmas({})
    saved = (D.INVENTORY_ACTIVE if hasattr(D, "INVENTORY_ACTIVE") else None)
    G.DED.set_active_inventory(pset, params)
    facts = []
    with G._restricted_inventory():
        avail = G._avail_for(S, record_views)
        extra = [dict(pr) for pr in numeric]
        for E in avail:
            extra.append({"coeffs": {k: int(v) for k, v in E["disp"]["coeffs"].items()},
                          "rel": E["disp"]["rel"], "rhs": int(E["disp"]["rhs"]), "text": f"__REC__{E['id']}"})
        d0 = {v: int(c) for v, c in canon["coeffs"].items() if int(c) != 0}
        ctx = Context(premises=extra, depth=0, use_conditional_split=False, use_bnb=False,
                      use_lemmas=False, extra_directions=[d0, G._neg(d0)], max_rounds=max_rounds)
        ctx.saturate()
        used_vars = set()
        seen = set()
        for f in ctx.facts:
            if f.rule not in _INPUT_RULES:
                continue
            # scale coeffs·x + const  (REL 0) to integers; emit as coeffs·x REL -const
            vals = list(f.coeffs.values()) + [f.const]
            L = 1
            for q in vals:
                L = L * q.denominator // gcd(L, q.denominator)
            coeffs = {v: int(c * L) for v, c in f.coeffs.items() if int(c * L) != 0}
            if not coeffs:
                continue
            rhs = int(-f.const * L)
            rel = "==" if f.rel == "==" else ">="
            key = (tuple(sorted(coeffs.items())), rel, rhs)
            if key in seen:
                continue
            seen.add(key)
            facts.append((coeffs, rel, rhs))
            used_vars |= set(coeffs)
    goal = ({v: int(c) for v, c in canon["coeffs"].items() if int(c) != 0}, canon["rel"], int(canon["rhs"]))
    used_vars |= set(goal[0])
    return facts, goal, sorted(used_vars)


def _render(coeffs, rel, rhs):
    terms = " + ".join(f"({c})*{_lean_var(v)}" for v, c in sorted(coeffs.items()))
    op = {">=": "≥", "<=": "≤", "==": "="}[rel]
    return f"{terms} {op} {rhs}"


def lean_theorem(name, facts, goal, variables):
    decls = " ".join(f"({_lean_var(v)} : Int)" for v in variables)
    hyps = " ".join(f"(h{i} : {_render(*f)})" for i, f in enumerate(facts))
    return f"theorem {name} {decls} {hyps} : {_render(*goal)} := by omega"


_OMEGA_HEADER = "import Mathlib"
_lean_runner = None


def _goal_statement(facts, goal, variables):
    """A closed proposition for an omega case: ``∀ (vars : Int), f0 → … → goal``.
    (lean_batch renders ``theorem name : <stmt> := by <proof>`` with no binder slot,
    so the hypotheses/binders are folded into the statement and introduced in the proof.)"""
    binder = ("(" + " ".join(_lean_var(v) for v in variables) + " : Int), ") if variables else ""
    parts = [f"({_render(*f)})" for f in facts] + [f"({_render(*goal)})"]
    return "∀ " + binder + " → ".join(parts) if variables else " → ".join(parts)


def omega_decide_batch(cases):
    """cases: list of (name, facts, goal, vars).  Returns ``({name: entailed_bool}, "", "")``.

    v1.4.6: routed through ``pf_trust.lean_batch.verify`` — a goal counts as entailed ONLY
    when the fail-closed summary positively confirms its declaration is present with axioms
    ⊆ ALLOWED_AXIOMS (no `sorryAx`); NOT_PROVEN and UNKNOWN both map to ``False`` (a wrong
    "entailed" would be unsound; "not entailed" is only incomplete).  Decision never comes
    from the absence of error messages.  ``-D maxErrors`` is passed as defense-in-depth so a
    mostly-failing batch does not abort and force splitting (speed only; correctness does
    not depend on it)."""
    from pf_trust import lean_batch as LB
    global _lean_runner
    if _lean_runner is None:
        _lean_runner = LB.lake_runner(str(_LEAN_DIR), extra_args=["-D", "maxErrors=100000000"])
    goals = [LB.Goal(f"thm_{i}", _goal_statement(f, g, v), "intros; omega")
             for i, (_n, f, g, v) in enumerate(cases)]
    res = LB.verify(goals, _OMEGA_HEADER, _lean_runner, max_batch=400)
    out = {}
    for i, (n, _f, _g, _v) in enumerate(cases):
        out[n] = res[f"thm_{i}"].verdict is LB.Verdict.PROVEN
    return out, "", ""


def complete_entails(props, numeric, canon, record_views, max_rounds=64):
    facts, goal, variables = collect_facts(props, numeric, canon, record_views, max_rounds)
    out, _src, _log = omega_decide_batch([("t", facts, goal, variables)])
    return out["t"]


# ════════════════════════════════════════════════════════════════════════════
# v1.4.3+ : COMPLETE usability (H4) + COMPLETE encoding (H3)
#
# The checker above decides which records are usable for a target T with
# ``G._avail_for`` — whose numeric-premise test is ``_restricted_entails`` (bounded
# LP + <=8 rounds; incomplete), and whose conditional-theorem firing happens during a
# bounded Context saturation.  A record whose premises follow from T's only by complete
# integer reasoning is then wrongly excluded, and its conclusion never reaches omega.
# The functions below replace BOTH gates by Lean ``omega`` (complete LIA):
#   * a record R is usable for T  iff  R's property premises are in T's property
#     closure (the is_tree ⇒ is_acyclic ⇒ is_bipartite / is_connected lattice via
#     ``property_closure``) AND omega proves every numeric premise of R from
#     (restricted Inventory active for T ∪ premises(T));
#   * a numeric-hypothesis conditional theorem (e.g. complete_indep: chi ≥ n ⇒ α ≤ 1)
#     fires iff omega proves its hypothesis from the current fact set (iterated to a
#     fixpoint), rather than via bounded saturation.
# The restricted Inventory families (property-conditioned facts such as is_tree ⇒
# tree_edges, is_bipartite ⇒ chi ≤ 2, regular ⇒ 2m = d·n, girth/cycle facts, the
# nonneg facts, and the linear unconditional facts) are already materialised by
# ``set_active_inventory`` for T's property closure and are all included.
# ════════════════════════════════════════════════════════════════════════════
_RELMAP = {"=": "==", ">": ">=", "<": "<="}


def _norm(rel):
    return _RELMAP.get(rel, rel)


def _ptuple(pr):
    return ({v: int(c) for v, c in pr["coeffs"].items() if int(c) != 0}, _norm(pr["rel"]), int(pr["rhs"]))


def active_restricted_facts(props, params):
    """(pset, inv_facts, conditionals) for property set ``props`` under the RESTRICTED
    inventory.  ``inv_facts`` = every active linear Inventory fact (unconditional +
    property-conditioned + nonneg) as ``(coeffs, rel, rhs)``.  ``conditionals`` =
    ``[(hyp_tuple, concl_tuple)]`` for the numeric-hypothesis theorems that survive the
    restricted (product-free) view (e.g. complete_indep)."""
    names = {p["name"] if isinstance(p, dict) else p for p in props}
    pset = G.property_closure(names)
    G.DED.set_active_inventory(pset, params)
    inv, conds = [], []
    with G._restricted_inventory():
        for e in G.DED.INVENTORY:
            c = e["conclusion"]
            coeffs = {v: int(x) for v, x in c["coeffs"].items() if int(x) != 0}
            if coeffs:
                inv.append((coeffs, _norm(c["rel"]), int(c["rhs"])))
        for e in G.DED.CONDITIONAL_THEOREMS:
            conds.append((_ptuple(e["hypothesis"]), _ptuple(e["conclusion"])))
    return pset, inv, conds


def _vars_of(facts, goal):
    s = set(goal[0])
    for (c, _r, _h) in facts:
        s |= set(c)
    return sorted(s)


def props_dischargeable(R_props, T_props, pset=None):
    """Can T's premises discharge R's property premises?  v1.4.6 §3: delegates to
    ``pf_trust.props.dischargeable`` (the single decision rule) with our
    ``property_closure`` as the non-parametric lattice; parametric properties
    (is_regular(d) exact, is_k_edge_connected(k) monotone) are matched by pf_trust,
    never stripped by the lattice.  ``pset`` is accepted for signature compatibility
    but ignored (the closure is recomputed from T's non-parametric names)."""
    from pf_trust.props import dischargeable as _pf_dischargeable
    return _pf_dischargeable(G._prop_strs(R_props), G._prop_strs(T_props),
                             closure=G.property_closure)


def collect_facts_complete(props, numeric, canon, record_views):
    """Complete-encoding + complete-usability variant of ``collect_facts``.  Returns
    ``(facts, goal, vars)`` where usable record conclusions and fired conditionals are
    decided by Lean ``omega`` (complete LIA), not by the bounded engine."""
    saved = (G.DED.INVENTORY, G.DED.PRODUCT_FACTS, G.DED.CONDITIONAL_THEOREMS, G.DED.INVENTORY_BY_NAME)
    try:
        params = {p["name"]: p.get("param") for p in props if "param" in p}
        pset, inv, conds = active_restricted_facts(props, params)
        tnum = [_ptuple(pr) for pr in numeric]
        base = tnum + inv
        goal = ({v: int(c) for v, c in canon["coeffs"].items() if int(c) != 0}, canon["rel"], int(canon["rhs"]))
        bvars = _vars_of(base, goal)

        # ── complete usability: property discharge (lattice + param match) + omega ──
        cand = [E for E in record_views if E["id"] is not None
                and props_dischargeable(E["props"], props, pset)]
        ucases = []
        for E in cand:
            for j, pr in enumerate(E["numeric"]):
                g = _ptuple(pr)
                vs = sorted(set(bvars) | set(g[0]))
                ucases.append((f"u_{E['id']}_{j}", base, g, vs))
        udec = omega_decide_batch(ucases)[0] if ucases else {}
        usable = [E for E in cand
                  if all(udec.get(f"u_{E['id']}_{j}", False) for j in range(len(E["numeric"])))]

        facts = list(base)
        for E in usable:
            d = E["disp"]
            facts.append(({v: int(c) for v, c in d["coeffs"].items() if int(c) != 0}, _norm(d["rel"]), int(d["rhs"])))

        # ── complete conditional firing (omega), iterated to a fixpoint ──
        present = {(tuple(sorted(c.items())), r, h) for (c, r, h) in facts}
        changed = True
        while changed:
            changed = False
            for (hyp, concl) in conds:
                key = (tuple(sorted(concl[0].items())), concl[1], concl[2])
                if key in present or not concl[0]:
                    continue
                vs = _vars_of(facts, (hyp[0], hyp[1], hyp[2]))
                if omega_decide_batch([("h", facts, hyp, vs)])[0]["h"]:
                    facts.append(concl); present.add(key); changed = True
        return facts, goal, _vars_of(facts, goal), {"usable": [E["id"] for E in usable], "n_cand": len(cand)}
    finally:
        (G.DED.INVENTORY, G.DED.PRODUCT_FACTS, G.DED.CONDITIONAL_THEOREMS, G.DED.INVENTORY_BY_NAME) = saved


def complete_entails_v2(props, numeric, canon, record_views):
    """Complete-usability + complete-encoding entailment (H3 + H4 fixed)."""
    facts, goal, variables, _meta = collect_facts_complete(props, numeric, canon, record_views)
    return omega_decide_batch([("t", facts, goal, variables)])[0]["t"]


def _selftest():
    """Sanity: omega decides a trivially-entailed and a trivially-unentailed case."""
    ok = omega_decide_batch([("pos", [({"a": 1}, ">=", 5)], ({"a": 1}, ">=", 3), ["a"]),
                             ("neg", [({"a": 1}, ">=", 3)], ({"a": 1}, ">=", 5), ["a"])])[0]
    assert ok["pos"] is True and ok["neg"] is False, ok
    print("closure_complete selftest OK:", ok)


if __name__ == "__main__":
    import sys
    if "--selftest" in sys.argv:
        _selftest()
    else:
        print("module: use complete_entails (restricted usability) / complete_entails_v2 (complete usability)")
