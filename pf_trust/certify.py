"""Two-sided certificates for a linear-integer entailment (v1.5 PHASE C3/C4/C5).

An omega case is: facts ``f_k`` entail a goal ``g``, all over INTEGER variables.
Each fact/goal is ``(coeffs: {var:int}, rel, rhs:int)`` meaning
``sum(coeffs[v]*v) REL rhs`` with ``REL in {">=","<=","==",">","<"}``.

``entailment_status`` asks an EXACT integer solver (z3, integer theory — a complete
decision procedure for the same Presburger/LIA fragment omega decides):

    facts entail goal  ⟺  (facts ∧ ¬goal) is UNSAT.

* NOT entailed  → z3 returns a concrete INTEGER model where every fact holds and the
  goal fails: a counterexample witness (C3).
* entailed      → (facts ∧ ¬goal) is UNSAT (C4).

``recheck_witness`` re-verifies a witness in PURE PYTHON with ``Fraction``/``int``
arithmetic (no floats, no z3): every premise must hold and the goal must fail. A
NOT_PROVEN whose witness fails this check, or a PROVEN that z3 finds satisfiable,
is a bug to investigate (encoding error / missing constraint / omega incompleteness
outside its fragment) — never silently accepted.
"""
from __future__ import annotations

from fractions import Fraction
from typing import Mapping, Sequence

Fact = tuple[Mapping[str, int], str, int]


def _int(x) -> int:
    """Accept only genuine integers (bools count). Reject floats/strings so a
    non-integer can never be SILENTLY truncated into a different value (v1.5 audit
    hardening): a float input is a caller bug, not something to round."""
    if isinstance(x, bool):
        return int(x)
    if isinstance(x, int):
        return x
    raise TypeError(f"integer required, got {type(x).__name__}: {x!r}")


def _lhs_value(coeffs: Mapping[str, int], model: Mapping[str, int]) -> Fraction:
    # exact: integer coeffs * integer assignment (no floats admitted)
    return sum((Fraction(_int(c)) * Fraction(_int(model[v])) for v, c in coeffs.items()),
               Fraction(0))


def _holds(fact: Fact, model: Mapping[str, int]) -> bool:
    coeffs, rel, rhs = fact
    lhs = _lhs_value(coeffs, model)
    rhs = Fraction(_int(rhs))
    if rel == ">=":
        return lhs >= rhs
    if rel == "<=":
        return lhs <= rhs
    if rel == "==":
        return lhs == rhs
    if rel == ">":
        return lhs > rhs
    if rel == "<":
        return lhs < rhs
    raise ValueError(f"unsupported relation {rel!r}")


def recheck_witness(facts: Sequence[Fact], goal: Fact, model: Mapping[str, int]) -> dict:
    """PURE-PYTHON exact re-check that ``model`` is a genuine counterexample:
    every fact holds and the goal FAILS. Returns a structured verdict."""
    model = {k: _int(v) for k, v in model.items()}      # reject non-integer witnesses
    bad_fact = next((i for i, f in enumerate(facts) if not _holds(f, model)), None)
    goal_holds = _holds(goal, model)
    ok = bad_fact is None and not goal_holds
    return {"ok": ok, "model": model,
            "all_premises_hold": bad_fact is None,
            "goal_fails": not goal_holds,
            "first_violated_premise": bad_fact}


def _z3_expr(solver_vars, coeffs, rel, rhs):
    import z3
    terms = [_int(c) * solver_vars[v] for v, c in coeffs.items()]
    lhs = z3.Sum(terms) if terms else z3.IntVal(0)
    rhs = z3.IntVal(_int(rhs))
    return {">=": lhs >= rhs, "<=": lhs <= rhs, "==": lhs == rhs,
            ">": lhs > rhs, "<": lhs < rhs}[rel]


def entailment_status(facts: Sequence[Fact], goal: Fact,
                      variables: Sequence[str] | None = None) -> dict:
    """Decide facts ⊨ goal over the integers with z3.

    Returns ``{"status": "entailed"|"refuted"|"unknown", "witness": {var:int}|None,
    "recheck": {...}|None}``. On "refuted" the witness is re-checked in pure Python;
    ``recheck["ok"]`` MUST be True (else the witness or encoding is bad)."""
    import z3
    varset = set(variables or [])
    for f in list(facts) + [goal]:
        varset |= set(f[0])
    zvars = {v: z3.Int(f"v_{v}") for v in sorted(varset)}
    s = z3.Solver()
    for f in facts:
        s.add(_z3_expr(zvars, *f))
    s.add(z3.Not(_z3_expr(zvars, *goal)))      # facts ∧ ¬goal
    r = s.check()
    if r == z3.unsat:
        return {"status": "entailed", "witness": None, "recheck": None}
    if r == z3.sat:
        m = s.model()
        model = {v: m.eval(zvars[v], model_completion=True).as_long() for v in zvars}
        recheck = recheck_witness(facts, goal, model)
        return {"status": "refuted", "witness": model, "recheck": recheck}
    return {"status": "unknown", "witness": None, "recheck": None}


PF_DECISION_MODULE = True  # v1.5: hashed into the omega verdict cache key (pf_trust/cachekey.py)
