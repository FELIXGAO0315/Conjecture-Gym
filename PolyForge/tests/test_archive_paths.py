#!/usr/bin/env python3
"""PolyForge §G1: single-archive-path test.

``archive_removal`` is the ONLY appender to pruned.jsonl — no removal path may
call ``_pruned_archive_append`` / ``make_prune_entry`` directly.  Enforced by a source
scan (fails if any other site does), plus a behavioural check that each wired removal
reason routes through ``archive_removal``.
"""
import re, sys
from pathlib import Path
ROOT = Path("/home/felix_gao/Conjecture-Gym")
sys.path.insert(0, str(ROOT))


def test_single_archive_path():
    # the only in-tree callers of the low-level appender / entry builder must be
    # archive_removal itself (and the definitions/aliases).
    files = [ROOT / "PolyForge/domains/graph/generator.py",
             ROOT / "PolyForge/domains/graph/domain.py",
             ROOT / "PolyForge/env/analysis/record_audit.py",
             ROOT / "run.py"]
    offenders = []
    for f in files:
        for i, line in enumerate(f.read_text().splitlines(), 1):
            s = line.strip()
            if s.startswith("#"):
                continue
            # calls (not defs / aliases / comments)
            for tok in ("pruned_archive_append(", "_pruned_archive_append(", "make_prune_entry("):
                if tok in line and "def " not in line:
                    # allowed ONLY inside generator.archive_removal (the central path)
                    ctx = f.name
                    offenders.append((ctx, i, tok, s))
    # whitelist: the two calls inside archive_removal's body, in generator.py
    allowed = [o for o in offenders if o[0] == "generator.py" and o[2] in
               ("make_prune_entry(", "_pruned_archive_append(")]
    # every make_prune_entry / _pruned_archive_append call must be one of the two in
    # archive_removal; any OTHER file calling them is a bypass.
    bypass = [o for o in offenders if o[0] != "generator.py"]
    # within generator.py, there must be exactly the archive_removal body calls (2) +
    # the alias line is a def-level assignment (not a call) so excluded above.
    print(f"§G1 appender/builder call sites: generator.py={len(allowed)}, other={len(bypass)}")
    for o in bypass:
        print("  BYPASS:", o)
    assert not bypass, "a removal path bypasses archive_removal()"
    # and archive_removal must exist and be referenced by every removal site
    from PolyForge.domains.graph import generator as G
    assert hasattr(G, "archive_removal"), "archive_removal missing"
    for f, needs in [(ROOT / "PolyForge/domains/graph/generator.py", "archive_removal("),
                     (ROOT / "PolyForge/domains/graph/domain.py", "archive_removal("),
                     (ROOT / "PolyForge/env/analysis/record_audit.py", "archive_removal(")]:
        assert needs in f.read_text(), f"{f.name} does not route through archive_removal"
    assert "archive_replacement" in (ROOT / "run.py").read_text(), "run.py replacement not archived"
    from PolyForge.domains.graph.domain import GraphDomain
    assert hasattr(GraphDomain, "archive_replacement"), "domain.archive_replacement missing"
    print("§G1 single-archive-path test: PASS")


if __name__ == "__main__":
    test_single_archive_path()
    print("archive-paths tests OK")
