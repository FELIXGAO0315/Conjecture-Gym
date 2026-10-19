"""Parameter-aware property dischargeability.

Bug found in v1.4.5: usability compared property NAMES only, so a record needing
`is_regular(3)` was treated as usable under `is_regular(2)`.

`dischargeable(required, available, closure)` answers: does every graph that has
all `available` properties also have all `required` properties? It is SOUND by
construction (may answer False when the truth is True, never the reverse):

* non-parametric required properties: must be in closure(non-parametric available),
  where `closure` is the project's own lattice function (property_closure);
* parametric required properties: discharged ONLY by a parametric available
  property of the same name, under PARAM_RULES; unknown parametric names need an
  exact match. Parametric properties are never passed to `closure`, so the lattice
  can never strip a parameter.
"""
from __future__ import annotations

import re
from typing import Callable, Iterable

_PROP_RE = re.compile(r"^\s*([A-Za-z_][A-Za-z0-9_]*)\s*(?:\(\s*([^)]*)\s*\))?\s*$")

# need, have: tuples of ints. True only when `have` implies `need` on every graph.
PARAM_RULES: dict[str, Callable[[tuple[int, ...], tuple[int, ...]], bool]] = {
    "is_regular": lambda need, have: need == have,                       # d-regular is d-regular only
    # k'-edge-conn ⇒ k-edge-conn (k ≤ k'). v1.5 audit hardening: require the exact
    # single-arg arity, so a malformed multi-arg form never discharges by inspecting
    # only have[0] (which would ignore the extra argument).
    "is_k_edge_connected": lambda need, have: len(need) == len(have) == 1 and have[0] >= need[0],
}

Prop = tuple[str, tuple[int, ...]]


def parse_prop(text: str) -> Prop:
    m = _PROP_RE.match(text)
    if not m:
        raise ValueError(f"unparseable property: {text!r}")
    name, args = m.group(1), m.group(2)
    if args is None or args.strip() == "":
        return name, ()
    return name, tuple(int(a.strip()) for a in args.split(","))


def format_prop(p: Prop) -> str:
    name, args = p
    return name if not args else f"{name}({','.join(map(str, args))})"


def dischargeable(required: Iterable[str], available: Iterable[str],
                  closure: Callable[[set[str]], set[str]]) -> bool:
    req = [parse_prop(r) for r in required]
    av = [parse_prop(a) for a in available]
    plain_av = {n for n, args in av if not args}
    param_av = [(n, args) for n, args in av if args]
    closed = set(closure(set(plain_av)))
    for name, args in req:
        if not args:
            if name not in closed:
                return False
            continue
        rule = PARAM_RULES.get(name, lambda need, have: need == have)
        if not any(n == name and rule(args, a) for n, a in param_av):
            return False
    return True


PF_DECISION_MODULE = True  # v1.5: hashed into the omega verdict cache key (pf_trust/cachekey.py)
