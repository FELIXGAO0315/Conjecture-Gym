from PolyForge.engine.soundness.audits import graph_soundness_violations, monotonicity_violations
from PolyForge.engine.soundness.lean_batch import Verdict
from PolyForge.engine.soundness.policies import Ent, decide_with_prefilter, from_lean, may_prune, may_replace


def test_only_exact_entailment_prunes():
    assert may_prune(Ent.ENTAILED)
    assert not may_prune(Ent.UNKNOWN) and not may_prune(Ent.NOT_ENTAILED)
    assert from_lean(Verdict.UNKNOWN) is Ent.UNKNOWN


def test_float_prefilter_cannot_conclude_entailed():
    calls = []
    exact = lambda p: calls.append(p) or Ent.NOT_ENTAILED
    # float solver says "maybe entailed" -> exact decides, result not overridden
    assert decide_with_prefilter("p", lambda p: False, exact) is Ent.NOT_ENTAILED
    assert calls == ["p"]
    # float solver says "not entailed" -> skip exact
    assert decide_with_prefilter("q", lambda p: True, exact) is Ent.NOT_ENTAILED
    assert calls == ["p"]


def test_replace_requires_usability_and_entailment():
    assert not may_replace("old", "new", lambda o, n: False, lambda o, rs: Ent.ENTAILED)
    assert not may_replace("old", "new", lambda o, n: True, lambda o, rs: Ent.UNKNOWN)
    assert may_replace("old", "new", lambda o, n: True, lambda o, rs: Ent.ENTAILED)


def test_monotonicity_and_graph_audits():
    pairs = [(1, 2), (3, 4)]
    v = monotonicity_violations(pairs, lambda t, r: True, lambda t, r: t == 1)
    assert v == [(3, 4)]
    # premise sets as Python predicates on an int "graph"
    prem = {1: lambda g: g >= 2, 2: lambda g: g >= 3}
    bad = graph_soundness_violations([(1, 2)], lambda t, r: True, range(10),
                                     lambda t, g: prem[t](g))
    assert bad == [(1, 2, 2)]
