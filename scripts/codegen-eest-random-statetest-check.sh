#!/usr/bin/env bash
# Run the EEST random_statetest stateless-guest regression windows.
#
# The zkevm@v0.4.0 random_statetest class has 503 stateless blocks. Split it
# into two windows so reruns can resume from the second half without starting
# from the beginning.
set -euo pipefail

cd "$(dirname "$0")/.."

JOBS="${EEST_RANDOM_JOBS:-${EEST_JOBS:-auto}}"
STEPS="${EEST_RANDOM_STEPS:-${EEST_STEPS:-200000000}}"

run_window() {
  local name="$1"
  local skip="$2"
  local limit="$3"
  local min_full="$4"
  shift 4

  echo "==> random_statetest ${name}: skip=${skip} limit=${limit}"
  scripts/codegen-eest-stateless-check.sh \
    --filter random_statetest \
    --skip "$skip" \
    --limit "$limit" \
    --jobs "$JOBS" \
    --quiet-passes \
    --max-failures 1 \
    --min-full "$min_full" \
    --steps "$STEPS" \
    "$@"
}

run_window "prefix" 0 200 200 "$@"
run_window "suffix" 200 500 303 "$@"

echo "==> PASS: random_statetest EEST regression windows full-match"
