#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
HOOK="$ROOT/.git/hooks/pre-push"
cp "$ROOT/scripts/pre-push-hook.sh" "$HOOK"
chmod +x "$HOOK"
echo "installed pre-push hook -> $HOOK"
