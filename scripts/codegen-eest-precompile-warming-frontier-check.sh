#!/usr/bin/env bash
# Probe a fast EIP-2929 precompile-warming frontier.
#
# The first selected fixture has the stateless root and tail matching today,
# but still fails the successful_validation bit. It is a compact signal for
# BALANCE/precompile warmness and transaction execution progress.
set -euo pipefail

cd "$(dirname "$0")/.."

JOBS="${EEST_PRECOMPILE_WARMING_JOBS:-${EEST_JOBS:-1}}"
STEPS="${EEST_PRECOMPILE_WARMING_STEPS:-${EEST_STEPS:-200000000}}"

scripts/codegen-eest-stateless-check.sh \
  --filter precompile_warming \
  --limit 1 \
  --jobs "$JOBS" \
  --quiet-passes \
  --max-failures 1 \
  --steps "$STEPS" \
  "$@"

echo "==> PASS: precompile-warming frontier probe completed"
