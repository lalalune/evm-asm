#!/usr/bin/env bash
# codegen-eest-failed-tx-paris-layout-check.sh
#
# The Paris failed_tx_xcf416c53 fixture has block_gas_limit=200,000,000.
# The current stateless_guest static layout is sized for 120,000,000, so the
# launcher must classify it as layout-incompatible before invoking ziskemu.
set -euo pipefail

cd "$(dirname "$0")/.."

TAG="${EEST_FIXTURE_TAG:-zkevm@v0.4.0}"
FX="${EEST_FIXTURES_DIR:-$(pwd)/gen-out/eest-fixtures/$TAG/fixtures/fixtures}"
[[ -d "$FX" ]] || { echo "fixtures not found at $FX (run scripts/eest-fetch-fixtures.sh '$TAG')" >&2; exit 1; }

RUN_DIR="${RUN_DIR:-gen-out/eest-failed-tx-paris-layout}"
case "$RUN_DIR" in
  /*) ;;
  *) RUN_DIR="$PWD/$RUN_DIR" ;;
esac
rm -rf "$RUN_DIR"
mkdir -p "$RUN_DIR"

LOG="${LOG:-gen-out/eest-failed-tx-paris-layout.log}"
case "$LOG" in
  /*) ;;
  *) LOG="$PWD/$LOG" ;;
esac
rm -f "$LOG"

echo "==> run failed_tx Paris layout-incompatible check"
scripts/codegen-eest-stateless-check.sh \
  --filter failed_tx_xcf416c53_paris \
  --limit 10 \
  --jobs 1 \
  --max-failures 1 \
  --quiet-passes \
  --steps "${EEST_FAILED_TX_PARIS_STEPS:-200000000}" \
  --run-dir "$RUN_DIR" \
  >"$LOG" 2>&1

require_log() {
  local pattern="$1"
  if ! grep -Fq "$pattern" "$LOG"; then
    echo "missing expected output: $pattern" >&2
    sed -n '1,220p' "$LOG" >&2
    exit 1
  fi
}

require_log "ERROR(layout)"
require_log "failed_tx_xcf416c53_paris.json"
require_log "gas_limit 200000000>120000000"
require_log "selected:    1"
require_log "errored:     1"
require_log "ran:         0"

if find "$RUN_DIR" -name '*.emu.log' -print -quit | grep -q .; then
  echo "unexpected ziskemu log found; layout-incompatible fixture should not launch guest" >&2
  find "$RUN_DIR" -name '*.emu.log' -print >&2
  exit 1
fi

echo "==> PASS: failed_tx Paris is classified layout-incompatible before guest launch"
