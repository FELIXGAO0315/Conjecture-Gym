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


def omega_decide_batch(cases):
    """cases: list of (name, facts, goal, vars).  Returns {name: entailed_bool} by
    compiling one Lean file with ``omega`` on each and parsing which failed."""
    lines = [lean_theorem(n, f, g, v) for (n, f, g, v) in cases]
    src = "\n".join(lines) + "\n"
    tmp = Path("/tmp/claude-1000/-home-felix-gao-Conjecture-Gym/8510a703-7b76-43e8-a494-f5f779f22746/scratchpad/omega_closure.lean")
    tmp.parent.mkdir(parents=True, exist_ok=True)
    tmp.write_text(src)
    res = subprocess.run(["lake", "env", "lean", str(tmp)], cwd=str(_LEAN_DIR),
                         capture_output=True, text=True)
    failed = set()
    for m in re.finditer(r"\.lean:(\d+):\d+: error", res.stdout + res.stderr):
        failed.add(int(m.group(1)))
    out = {}
    for i, (n, _f, _g, _v) in enumerate(cases):
        out[n] = (i + 1) not in failed          # line i+1 errored ⇒ not entailed
    return out, src, res.stdout + res.stderr


def complete_entails(props, numeric, canon, record_views, max_rounds=64):
    facts, goal, variables = collect_facts(props, numeric, canon, record_views, max_rounds)
    out, _src, _log = omega_decide_batch([("t", facts, goal, variables)])
    return out["t"]


if __name__ == "__main__":
    print("module: use complete_entails / omega_decide_batch")
