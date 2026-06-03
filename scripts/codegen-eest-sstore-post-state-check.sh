#!/usr/bin/env bash
# Probe SSTORE-shaped EEST fixtures that exercise BAL storage-change replay into
# post-state-root recomputation.
#
# Defaults to a compact smoke window. Pass extra arguments through to
# codegen-eest-stateless-check.sh, for example `--limit 0` for the full current
# filter set or a custom `--run-dir`.
set -euo pipefail

cd "$(dirname "$0")/.."

JOBS="${EEST_SSTORE_POST_STATE_JOBS:-${EEST_JOBS:-1}}"
STEPS="${EEST_SSTORE_POST_STATE_STEPS:-${EEST_STEPS:-200000000}}"
LIMIT="${EEST_SSTORE_POST_STATE_LIMIT:-20}"
MAX_FAILURES="${EEST_SSTORE_POST_STATE_MAX_FAILURES:-1}"

scripts/codegen-eest-stateless-check.sh \
  --filter sstore \
  --limit "$LIMIT" \
  --jobs "$JOBS" \
  --quiet-passes \
  --max-failures "$MAX_FAILURES" \
  --steps "$STEPS" \
  "$@"

echo "==> PASS: SSTORE post-state EEST probe completed"
