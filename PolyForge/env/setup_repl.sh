#!/usr/bin/env bash
# Build the Lean REPL used by the PolyForge verifier.
#
# We pin leanprover-community/repl at the tag v4.34.0 (commit
# 193cf4bb9a22bb3fc6d25774f0fe6a70db1fd6ee), which ships the Lean toolchain
# `leanprover/lean4:v4.34.0` — byte-for-byte the toolchain used by the graph
# domain's Lean project (PolyForge/domains/graph/lean).  The build output lives
# under PolyForge/env/vendor/ and is git-ignored; re-run this script on a fresh
# checkout before using the verifier.
set -euo pipefail

REPL_COMMIT="193cf4bb9a22bb3fc6d25774f0fe6a70db1fd6ee"   # tag v4.34.0
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
VENDOR="$HERE/vendor"
DEST="$VENDOR/repl"

mkdir -p "$VENDOR"
if [ ! -d "$DEST/.git" ]; then
  rm -rf "$DEST"
  git clone https://github.com/leanprover-community/repl.git "$DEST"
fi
cd "$DEST"
git fetch --all --tags --quiet || true
git checkout --quiet "$REPL_COMMIT"
lake build
echo "REPL built: $DEST/.lake/build/bin/repl"
