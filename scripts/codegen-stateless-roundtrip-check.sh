#!/usr/bin/env bash
# codegen-stateless-roundtrip-check.sh -- Stateless guest PR2 verification.
#
# Builds the `stateless_guest` program through codegen -> as -> ld,
# runs the resulting ELF on ziskemu, and diffs the first 41 bytes of
# ziskemu's public output against the expected SSZ encoding of the
# stub `StatelessValidationResult` defined in
# `EvmAsm/Stateless/SSZ/Encode/Program.lean`.
#
# Expected wire layout (41 bytes, all fixed-size SSZ Container):
#   bytes  0..32 : new_payload_request_root = 0x00..00 (32 bytes)
#   byte      32 : successful_validation    = 0x00     (false)
#   bytes 33..41 : chain_config.chain_id    = LE(1) = [01, 00 .. 00]
#
# This is the PR2 stub -- once the SSZ decoder lands and feeds real
# values, the expected bytes will derive from the Python reference's
# `SszStatelessValidationResult.encode_bytes(...)` over a fixture
# `StatelessInput`. For now we just verify the encoder path round-trips
# on ziskemu.
#
# Exit:
#   0 -- output matches expected
#   1 -- emission / build / emulation failed, or output mismatch
set -euo pipefail

cd "$(dirname "$0")/.."

# 82 hex chars = 41 bytes. See `EvmAsm/Stateless/SSZ/Encode/Program.lean`
# header for the field-by-field breakdown.
EXPECTED_HEX="0000000000000000000000000000000000000000000000000000000000000000000100000000000000"

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

echo "==> lake build codegen"
lake build codegen

echo "==> emit stateless_guest ELF"
lake exe codegen --program stateless_guest --halt linux93 \
  -o gen-out/stateless_guest

echo "==> ziskemu -e gen-out/stateless_guest.elf -o gen-out/stateless_guest.output"
"$ZISKEMU" -e gen-out/stateless_guest.elf \
  -o gen-out/stateless_guest.output -n 100000 \
  >gen-out/stateless_guest.emu.log 2>&1

# First 41 bytes of the output buffer = the SSZ-encoded result.
ACTUAL_HEX="$(xxd -p -l 41 gen-out/stateless_guest.output | tr -d '\n')"

echo
echo "expected (41 bytes, SSZ StatelessValidationResult stub):"
echo "  $EXPECTED_HEX"
echo "actual:"
echo "  $ACTUAL_HEX"
echo

if [[ "$ACTUAL_HEX" == "$EXPECTED_HEX" ]]; then
  echo "==> PASS: stateless_guest output matches expected SSZ stub"
  exit 0
else
  echo "==> FAIL: stateless_guest output mismatch"
  exit 1
fi
