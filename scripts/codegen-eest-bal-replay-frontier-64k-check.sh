#!/usr/bin/env bash
# Run the BAL replay frontier with the experimental 64 KiB block_state_root
# witness cap. This locks in the current measured progress: the smaller
# withdrawal-request case full-matches and only the large 170 KiB witness case
# remains a conservative miss.
set -euo pipefail

cd "$(dirname "$0")/.."

JOBS="${EEST_BAL_REPLAY_JOBS:-${EEST_JOBS:-auto}}"
STEPS="${EEST_BAL_REPLAY_STEPS:-${EEST_STEPS:-400000000}}"
BSR_WITNESS_CAP="${EEST_BSR_WITNESS_CAP:-65536}"

scripts/codegen-eest-stateless-check.sh \
  --filter withdrawal_requests \
  --skip 83 \
  --limit 20 \
  --jobs "$JOBS" \
  --quiet-passes \
  --bsr-witness-cap "$BSR_WITNESS_CAP" \
  --steps "$STEPS" \
  --min-full 19 \
  "$@"

echo "==> PASS: BAL replay frontier reaches 19/20 full matches with bsr_witness_cap=$BSR_WITNESS_CAP"
