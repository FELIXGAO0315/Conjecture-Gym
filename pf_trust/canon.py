"""Canonical form and content key for linear integer propositions.

A constraint is `sum(coef[v] * v) + const  OP  0` with OP in {">=", "=="}, all
values integers (graph invariants are integers). Canonicalisation:

* `<=` is turned into `>=` by negation; terms with zero coefficient are dropped;
* g = gcd of the variable coefficients;
  - ">=": divide coefficients by g and replace const by floor(const / g)
          (integer tightening: 2x - 3 >= 0  ->  x - 2 >= 0;  2x + 3 >= 0 -> x + 1 >= 0)
  - "==": if g does not divide const the constraint is unsatisfiable -> FALSE;
          otherwise divide, and make the first coefficient (by variable name) positive;
* no variables: TRUE if it holds, FALSE otherwise.

A proposition is (properties, premises, conclusion). Its key is the SHA-256 of a
canonical JSON of: sorted canonical properties, sorted de-duplicated canonical
premises, canonical conclusion.
"""
from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass
from math import gcd
from typing import Iterable, Mapping

from .props import format_prop, parse_prop

TRUE = ("TRUE",)
FALSE = ("FALSE",)


@dataclass(frozen=True)
class Lin:
    coefs: Mapping[str, int]
    const: int
    op: str  # ">=", "<=", "=="


def canon(c: Lin):
    if c.op not in (">=", "<=", "=="):
        raise ValueError(f"unsupported op {c.op!r}")
    sign = -1 if c.op == "<=" else 1
    coefs = {v: sign * int(k) for v, k in c.coefs.items() if int(k) != 0}
    const = sign * int(c.const)
    op = "==" if c.op == "==" else ">="
    if not coefs:
        holds = const >= 0 if op == ">=" else const == 0
        return TRUE if holds else FALSE
    g = 0
    for k in coefs.values():
        g = gcd(g, abs(k))
    if op == ">=":
        coefs = {v: k // g for v, k in coefs.items()}
        const = const // g          # Python // is floor division, also for negatives
    else:
        if const % g != 0:
            return FALSE
        coefs = {v: k // g for v, k in coefs.items()}
        const //= g
        first = coefs[min(coefs)]
        if first < 0:
            coefs = {v: -k for v, k in coefs.items()}
            const = -const
    return (op, tuple(sorted(coefs.items())), const)


def content_key(properties: Iterable[str], premises: Iterable[Lin], conclusion: Lin) -> str:
    props = sorted({format_prop(parse_prop(p)) for p in properties})
    prem = sorted({json.dumps(cp) for cp in (canon(p) for p in premises) if cp != TRUE})
    payload = {"props": props, "premises": prem, "conclusion": json.dumps(canon(conclusion))}
    return hashlib.sha256(json.dumps(payload, sort_keys=True).encode()).hexdigest()


PF_DECISION_MODULE = True  # v1.5: hashed into the omega verdict cache key (pf_trust/cachekey.py)
