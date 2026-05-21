#!/usr/bin/env bash
# codegen-zisk-hp-encode-nibbles-check.sh -- PR-K32.
#
# HP-encode a nibble array + leaf/extension flag into the byte
# string used as item 0 of MPT leaf/extension nodes. Inverse of
# PR-K23 hp_decode_nibbles.
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

echo "==> emit zisk_hp_encode_nibbles ELF"
lake exe codegen --program zisk_hp_encode_nibbles --halt linux93 \
  -o gen-out/zisk_hp_encode_nibbles

REPO_ROOT="$(pwd)"

# Python helper: HP-encode (nibbles, is_leaf) → bytes.
hp_encode() {
  python3 -c "
import sys
nibbles_hex = sys.argv[1]
is_leaf = int(sys.argv[2])
nibbles = [int(c, 16) for c in nibbles_hex]
flag = 2 if is_leaf else 0
if len(nibbles) % 2 == 1:
    flag |= 1
    result = bytes([flag * 0x10 + nibbles[0]])
    nibbles = nibbles[1:]
else:
    result = bytes([flag * 0x10])
for i in range(0, len(nibbles), 2):
    result += bytes([nibbles[i] * 0x10 + nibbles[i+1]])
print(result.hex())
" "$1" "$2"
}

run_case() {
  local name="$1" nibbles_hex="$2" is_leaf="$3"

  local in_file="$REPO_ROOT/gen-out/zisk_hp_encode_nibbles_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_hp_encode_nibbles_${name}.output"

  local nibble_count=${#nibbles_hex}
  local expected_hex
  expected_hex="$(hp_encode "$nibbles_hex" "$is_leaf")"

  # Build input: nibble_count (u64), is_leaf (u64), then nibbles as bytes (0..15 each).
  python3 -c "
import struct, sys
nibbles_hex = '$nibbles_hex'
is_leaf = $is_leaf
nibble_count = len(nibbles_hex)
nibble_bytes = bytes(int(c, 16) for c in nibbles_hex)
with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', nibble_count))
    f.write(struct.pack('<Q', is_leaf))
    f.write(nibble_bytes)
    total = 16 + nibble_count
    pad = (-total) % 8
    if pad:
        f.write(b'\x00' * pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_hp_encode_nibbles.elf \
    -i "$in_file" -o "$out_file" -n 100000 \
    >"$REPO_ROOT/gen-out/zisk_hp_encode_nibbles_${name}.emu.log" 2>&1 || true

  local expected_len=$(( ${#expected_hex} / 2 ))
  local actual_count actual_bytes exp_count_le
  actual_count="$(xxd -p -l 8 "$out_file" 2>/dev/null | tr -d '\n')"
  actual_bytes="$(dd if="$out_file" bs=1 skip=8 count="$expected_len" 2>/dev/null | xxd -p | tr -d '\n')"
  exp_count_le="$(python3 -c "print(int('$expected_len').to_bytes(8, 'little').hex())")"

  if [[ "$actual_count" == "$exp_count_le" && "$actual_bytes" == "$expected_hex" ]]; then
    printf "  %-26s OK   count=%d hp='%s'\n" "$name" "$expected_len" "$expected_hex"
    return 0
  else
    printf "  %-26s FAIL\n    expected: count=%d hp=%s\n    actual:   count=0x%s hp=%s\n" \
      "$name" "$expected_len" "$expected_hex" "$actual_count" "$actual_bytes"
    return 1
  fi
}

FAILED=0
# Empty nibbles, extension: HP byte = 0x00.
run_case "ext_empty"        ""            0   || FAILED=1
# Empty nibbles, leaf: HP byte = 0x20.
run_case "leaf_empty"       ""            1   || FAILED=1
# Single nibble, extension odd.
run_case "ext_odd_5"        "5"           0   || FAILED=1
# Single nibble, leaf odd.
run_case "leaf_odd_a"       "a"           1   || FAILED=1
# 2 nibbles, even extension.
run_case "ext_even_12"      "12"          0   || FAILED=1
# 2 nibbles, even leaf.
run_case "leaf_even_34"     "34"          1   || FAILED=1
# 3 nibbles, odd extension.
run_case "ext_odd_abc"      "abc"         0   || FAILED=1
# 3 nibbles, odd leaf.
run_case "leaf_odd_fee"     "fee"         1   || FAILED=1
# Long even.
run_case "long_even_ext"    "0102030405060708"  0   || FAILED=1
# Long odd.
run_case "long_odd_leaf"    "0102030405060708"  1   || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: hp_encode_nibbles emits canonical HP bytes for all input shapes"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
