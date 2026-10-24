"""PolyForge domains: pluggable mathematical subjects behind a common engine.

``load_domain(name)`` returns the domain instance.  The project is graph-only
(``graph.domain.GraphDomain``); the engine stays domain-agnostic so a new subject
is a new module implementing ``domains/base.py``, not an engine rewrite.
"""

from __future__ import annotations

DOMAIN_NAMES = ("graph",)


def load_domain(name: str):
    if name == "graph":
        from .graph.domain import GraphDomain
        return GraphDomain()
    raise ValueError(f"unknown domain: {name!r} (expected one of {DOMAIN_NAMES})")
