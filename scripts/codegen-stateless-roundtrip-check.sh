#!/usr/bin/env bash
# codegen-stateless-roundtrip-check.sh -- Stateless guest PR3 verification.
#
# Builds the `stateless_guest` program through codegen -> as -> ld,
# generates an SSZ-encoded `SszStatelessInput` (via the
# `execution-specs` reference library) carrying a known `chain_id`,
# feeds it to ziskemu, and diffs the first 41 bytes of ziskemu's
# public output against the expected SSZ encoding of
# `SszStatelessValidationResult(root = 0, valid = false,
#                              chain_id = <input chain_id>)`.
#
# The shape of the test:
#   1. Python builds a real `SszStatelessInput` with `chain_id = N`
#      and writes the length-prefixed file ziskemu expects.
#   2. Guest reads `chain_id` at `INPUT_ADDR + 24` (see
#      `EvmAsm/Stateless/SSZ/Decode/Program.lean`) and feeds it to the
#      encoder.
#   3. Encoder writes 41 SSZ bytes at `OUTPUT_ADDR`
#      (`EvmAsm/Stateless/SSZ/Encode/Program.lean`).
#   4. We compare output bytes against the Python-derived expected.
#
# Test fixtures (overridable via $CHAIN_ID): two values, including
# one that exercises all 8 bytes of the chain_id LE encoding.
#
# Exit:
#   0 -- both fixtures match expected
#   1 -- emission / build / emulation failed, or output mismatch
set -euo pipefail

cd "$(dirname "$0")/.."

ZISKEMU="${ZISKEMU:-}"
if [[ -z "$ZISKEMU" ]]; then
  if command -v ziskemu >/dev/null 2>&1; then
    ZISKEMU="$(command -v ziskemu)"
  elif [[ -x "$HOME/.zisk/bin/ziskemu" ]]; then
    ZISKEMU="$HOME/.zisk/bin/ziskemu"
  else
    echo "ziskemu not found -- install via ziskup or set ZISKEMU=..." >&2
    exit 1
  fi
fi

mkdir -p gen-out

REPO_ROOT="$(pwd)"
INPUT_GEN="$REPO_ROOT/scripts/stateless-gen-input.py"

echo "==> lake build codegen"
lake build codegen

echo "==> emit stateless_guest ELF"
lake exe codegen --program stateless_guest --halt linux93 \
  -o gen-out/stateless_guest

# Hex-encode a chain_id as the 16 hex chars that should appear at
# bytes 33..41 of the output (u64 LE).
chain_id_le_hex() {
  python3 -c "
import sys
c = int(sys.argv[1], 0)
print(c.to_bytes(8, 'little').hex())
" "$1"
}

# Build the 82-hex-char expected output for a given chain_id:
#   32 zero bytes (hash) | 1 zero byte (bool false) | 8 LE bytes of chain_id
expected_hex_for() {
  local cid="$1"
  local low7
  low7="$(chain_id_le_hex "$cid")"
  echo "$(printf '00%.0s' $(seq 1 33))${low7}"
}

run_fixture() {
  local cid="$1"
  local input_file="$REPO_ROOT/gen-out/stateless_guest-${cid//[^0-9A-Fa-fx]/_}.input"
  local output_file="$REPO_ROOT/gen-out/stateless_guest-${cid//[^0-9A-Fa-fx]/_}.output"
  local log_file="$REPO_ROOT/gen-out/stateless_guest-${cid//[^0-9A-Fa-fx]/_}.emu.log"

  echo "==> [chain_id=$cid] gen SSZ input"
  uv run --directory execution-specs --quiet python3 \
    "$INPUT_GEN" "$cid" "$input_file"

  echo "==> [chain_id=$cid] ziskemu run"
  "$ZISKEMU" -e gen-out/stateless_guest.elf -i "$input_file" \
    -o "$output_file" -n 100000 >"$log_file" 2>&1

  local actual expected
  actual="$(xxd -p -l 41 "$output_file" | tr -d '\n')"
  expected="$(expected_hex_for "$cid")"

  echo "    expected: $expected"
  echo "    actual:   $actual"

  if [[ "$actual" == "$expected" ]]; then
    echo "    PASS"
    return 0
  else
    echo "    FAIL"
    return 1
  fi
}

fail=0
for cid in "${CHAIN_ID:-1 0x1234567890ABCDEF}"; do
  for c in $cid; do
    if ! run_fixture "$c"; then
      fail=1
    fi
  done
done

if [[ "$fail" -eq 0 ]]; then
  echo "==> PASS: all stateless_guest fixtures match expected SSZ output"
  exit 0
else
  echo "==> FAIL: at least one fixture mismatched"
  exit 1
fi
