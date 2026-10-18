#!/usr/bin/env bash
# PolyForge v1.5 pre-push hook: run the FAST verification tier; block the push on failure.
# Skip with:  PF_SKIP_VERIFY=1 git push
if [ "${PF_SKIP_VERIFY:-0}" = "1" ]; then
  echo "pre-push: PF_SKIP_VERIFY=1 set, skipping verify_all FAST"; exit 0
fi
ROOT="$(git rev-parse --show-toplevel)"
echo "pre-push: running scripts/verify_all.sh FAST ..."
"$ROOT/scripts/verify_all.sh" FAST
