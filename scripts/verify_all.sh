#!/usr/bin/env bash
# PolyForge v1.5 PHASE G — one-command verification.
#
#   scripts/verify_all.sh            # FAST (<10 min): pins, all pytest suites
#                                    #   (incl. real-toolchain canaries + D fixtures),
#                                    #   published records byte-identical to the tag,
#                                    #   tag unmoved.
#   scripts/verify_all.sh FULL       # FAST + cold-matrix recompute + witness re-check
#                                    #   + oracle/anti-cheat/recompile + baselines
#                                    #   (from persisted results). PASS/FAIL per gate;
#                                    #   nonzero exit on any failure.
#
# Prints a RESULT_HASH over the decision-relevant content (timestamp-free), so two FULL
# runs from a clean checkout can be compared for hash identity.
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
MODE="${1:-FAST}"
exec python3 analysis/v1.5/verify_gates.py "$MODE"
