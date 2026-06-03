#!/usr/bin/env bash
# codegen-eest-eip8037-layout-check.sh
#
# EIP-8037 state_gas_pricing includes fixtures with block_gas_limit above the
# current stateless_guest static layout cap. The harness must classify those as
# layout-incompatible before invoking ziskemu; they require a larger-layout ELF,
# not a guest execution attempt.
set -euo pipefail

cd "$(dirname "$0")/.."

TAG="${EEST_FIXTURE_TAG:-zkevm@v0.4.0}"
FX="${EEST_FIXTURES_DIR:-$(pwd)/gen-out/eest-fixtures/$TAG/fixtures/fixtures}"
[[ -d "$FX" ]] || { echo "fixtures not found at $FX (run scripts/eest-fetch-fixtures.sh '$TAG')" >&2; exit 1; }

RUN_DIR="${RUN_DIR:-gen-out/eest-eip8037-layout}"
case "$RUN_DIR" in
  /*) ;;
  *) RUN_DIR="$PWD/$RUN_DIR" ;;
esac
rm -rf "$RUN_DIR"
mkdir -p "$RUN_DIR"

LOG="${LOG:-gen-out/eest-eip8037-layout.log}"
case "$LOG" in
  /*) ;;
  *) LOG="$PWD/$LOG" ;;
esac
rm -f "$LOG"

echo "==> run EIP-8037 layout-incompatible check"
scripts/codegen-eest-stateless-check.sh \
  --filter pricing_at_various_gas_limits \
  --skip 2 \
  --limit 1 \
  --jobs 1 \
  --max-failures 1 \
  --quiet-passes \
  --steps "${EEST_EIP8037_LAYOUT_STEPS:-200000000}" \
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
require_log "pricing_at_various_gas_limits.json"
require_log "gas_limit 1000000000>120000000"
require_log "selected:    1"
require_log "errored:     1"
require_log "ran:         0"

if find "$RUN_DIR" -name '*.emu.log' -print -quit | grep -q .; then
  echo "unexpected ziskemu log found; layout-incompatible fixture should not launch guest" >&2
  find "$RUN_DIR" -name '*.emu.log' -print >&2
  exit 1
fi

echo "==> PASS: EIP-8037 high-gas fixture is classified layout-incompatible before guest launch"
