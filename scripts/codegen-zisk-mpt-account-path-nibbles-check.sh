#!/usr/bin/env bash
# codegen-zisk-mpt-account-path-nibbles-check.sh -- PR-K100.
#
# Compute keccak256(input) and unpack into 64 nibbles.
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

echo "==> lake build codegen"
lake build codegen

echo "==> emit zisk_mpt_account_path_nibbles ELF"
lake exe codegen --program zisk_mpt_account_path_nibbles --halt linux93 \
  -o gen-out/zisk_mpt_account_path_nibbles

REPO_ROOT="$(pwd)"

# run_case <name> <input_hex>
run_case() {
  local name="$1" input="$2"

  local in_file="$REPO_ROOT/gen-out/zisk_mpt_account_path_nibbles_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_mpt_account_path_nibbles_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys
from Crypto.Hash import keccak
inp = bytes.fromhex('$input')
digest = keccak.new(digest_bits=256).update(inp).digest()
nibbles = bytearray(64)
for i, b in enumerate(digest):
    nibbles[2*i]   = b >> 4
    nibbles[2*i+1] = b & 0xf
with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(inp)))
    f.write(inp)
    pad = (-(8 + len(inp))) % 8
    if pad: f.write(b'\x00' * pad)
with open(sys.argv[1] + '.expected', 'wb') as f:
    f.write(nibbles)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_mpt_account_path_nibbles.elf \
    -i "$in_file" -o "$out_file" -n 1000000 \
    >"$REPO_ROOT/gen-out/zisk_mpt_account_path_nibbles_${name}.emu.log" 2>&1 || true

  local actual_status; actual_status="$(xxd -p -l 8 "$out_file" | tr -d '\n')"
  local actual_nibbles; actual_nibbles="$(dd if="$out_file" bs=1 skip=8 count=64 2>/dev/null | xxd -p | tr -d '\n')"
  local expected_nibbles; expected_nibbles="$(xxd -p "$in_file.expected" | tr -d '\n')"

  if [[ "$actual_status" == "0000000000000000" && "$actual_nibbles" == "$expected_nibbles" ]]; then
    printf "  %-32s OK\n" "$name"
    return 0
  else
    printf "  %-32s FAIL\n" "$name"
    printf "    actual:   %s\n" "${actual_nibbles:0:64}.."
    printf "    expected: %s\n" "${expected_nibbles:0:64}.."
    return 1
  fi
}

ZERO_ADDR="0000000000000000000000000000000000000000"
ALICE="aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
BOB="bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"
SLOT_ZERO="0000000000000000000000000000000000000000000000000000000000000000"
SLOT_ONE="0000000000000000000000000000000000000000000000000000000000000001"

FAILED=0
run_case "zero_address"     "$ZERO_ADDR"  || FAILED=1
run_case "alice"            "$ALICE"      || FAILED=1
run_case "bob"              "$BOB"        || FAILED=1
run_case "slot_zero"        "$SLOT_ZERO"  || FAILED=1
run_case "slot_one"         "$SLOT_ONE"   || FAILED=1
run_case "empty_input"      ""            || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: mpt_account_path_nibbles unpacks keccak256 into 64 nibbles"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
