#!/usr/bin/env bash
# Run the third EEST stateless-guest regression window after random_statetest
# in zkevm@v0.4.0 fixture order.
#
# This gate starts at skip 19085 and covers 1000 selected stateless blocks. It
# currently permits the known exp_power256 conservative state-root miss.
set -euo pipefail

cd "$(dirname "$0")/.."

JOBS="${EEST_POST_RANDOM_JOBS:-${EEST_JOBS:-auto}}"
STEPS="${EEST_POST_RANDOM_STEPS:-${EEST_STEPS:-200000000}}"

scripts/codegen-eest-stateless-check.sh \
  --skip 19085 \
  --limit 1000 \
  --jobs "$JOBS" \
  --quiet-passes \
  --max-failures 5 \
  --min-full 999 \
  --steps "$STEPS" \
  "$@"

echo "==> PASS: post-random EEST window 3 matches at least 999/1000"
