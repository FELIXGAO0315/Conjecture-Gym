"""PolyForge domains: pluggable mathematical subjects behind a common engine.

``load_domain(name)`` returns the domain instance for ``"hex"`` or ``"graph"``.
The hex domain is fully wired; the graph domain is a skeleton (see
``graph.domain.GraphDomain``).
"""

from __future__ import annotations

DOMAIN_NAMES = ("hex", "graph")


def load_domain(name: str):
    if name == "hex":
        from .hex.domain import HexDomain
        return HexDomain()
    if name == "graph":
        from .graph.domain import GraphDomain
        return GraphDomain()
    raise ValueError(f"unknown domain: {name!r} (expected one of {DOMAIN_NAMES})")
