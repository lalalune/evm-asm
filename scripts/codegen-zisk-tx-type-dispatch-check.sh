#!/usr/bin/env bash
# codegen-zisk-tx-type-dispatch-check.sh -- PR-K40.
#
# Dispatch a typed Ethereum transaction by its first byte.
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

echo "==> emit zisk_tx_type_dispatch ELF"
lake exe codegen --program zisk_tx_type_dispatch --halt linux93 \
  -o gen-out/zisk_tx_type_dispatch

REPO_ROOT="$(pwd)"

run_case() {
  local name="$1" tx_hex="$2" expected_status="$3" expected_type="$4" expected_offset="$5"

  local in_file="$REPO_ROOT/gen-out/zisk_tx_type_dispatch_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_tx_type_dispatch_${name}.output"

  python3 -c "
import struct, sys
tx = bytes.fromhex('$tx_hex')
with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(tx)))
    f.write(tx)
    pad = (-(8 + len(tx))) % 8
    if pad:
        f.write(b'\x00' * pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_tx_type_dispatch.elf \
    -i "$in_file" -o "$out_file" -n 5000 \
    >"$REPO_ROOT/gen-out/zisk_tx_type_dispatch_${name}.emu.log" 2>&1 || true

  local actual_status actual_type actual_offset
  actual_status="$(xxd -p -l 8 "$out_file" 2>/dev/null | tr -d '\n')"
  actual_type="$(dd if="$out_file" bs=1 skip=8 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  actual_offset="$(dd if="$out_file" bs=1 skip=16 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local exp_status_le exp_type_le exp_offset_le
  exp_status_le="$(python3 -c "print(int('$expected_status').to_bytes(8, 'little').hex())")"
  exp_type_le="$(python3 -c "print(int('$expected_type').to_bytes(8, 'little').hex())")"
  exp_offset_le="$(python3 -c "print(int('$expected_offset').to_bytes(8, 'little').hex())")"

  if [[ "$actual_status" == "$exp_status_le" && \
        "$actual_type" == "$exp_type_le" && \
        "$actual_offset" == "$exp_offset_le" ]]; then
    printf "  %-20s OK   status=%d type=%d offset=%d\n" "$name" "$expected_status" "$expected_type" "$expected_offset"
    return 0
  else
    printf "  %-20s FAIL  expected status=%d type=%d offset=%d actual: 0x%s 0x%s 0x%s\n" \
      "$name" "$expected_status" "$expected_type" "$expected_offset" \
      "$actual_status" "$actual_type" "$actual_offset"
    return 1
  fi
}

FAILED=0
# Legacy: byte 0 is RLP list prefix (0xc0..0xff). 0xf8 is common for long lists.
run_case "legacy_long_list"    "f87b80820fa08252089400112233445566778899aabbccddeeff001122338088ffffffffffffffff00"  0 0 0  || FAILED=1
run_case "legacy_short_list"   "c10180"                                                                                  0 0 0  || FAILED=1
# Typed
run_case "eip2930_type1"       "01abcdef"                                                                                  0 1 1  || FAILED=1
run_case "eip1559_type2"       "02abcdef"                                                                                  0 2 1  || FAILED=1
run_case "eip4844_type3"       "03abcdef"                                                                                  0 3 1  || FAILED=1
run_case "eip7702_type4"       "04abcdef"                                                                                  0 4 1  || FAILED=1
# Invalid first bytes
run_case "byte_00"             "00abcd"                                                                                    1 0 0  || FAILED=1
run_case "byte_05"             "05"                                                                                        1 0 0  || FAILED=1
run_case "byte_7f"             "7f"                                                                                        1 0 0  || FAILED=1
run_case "byte_80_short_str"   "80"                                                                                        1 0 0  || FAILED=1
run_case "byte_bf_long_str"    "bf"                                                                                        1 0 0  || FAILED=1
# Empty input
run_case "empty"               ""                                                                                          1 0 0  || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: tx_type_dispatch handles legacy + typed + invalid bytes"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
