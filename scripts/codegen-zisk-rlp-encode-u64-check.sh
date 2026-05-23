#!/usr/bin/env bash
# codegen-zisk-rlp-encode-u64-check.sh -- PR-K155.
#
# Encode a u64 directly as canonical RLP (convenience wrapper).
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

echo "==> emit zisk_rlp_encode_u64 ELF"
lake exe codegen --program zisk_rlp_encode_u64 --halt linux93 \
  -o gen-out/zisk_rlp_encode_u64

REPO_ROOT="$(pwd)"

# run_case <name> <value_u64>
run_case() {
  local name="$1" v="$2"

  local in_file="$REPO_ROOT/gen-out/zisk_rlp_encode_u64_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_rlp_encode_u64_${name}.output"
  local exp_hex_file="$REPO_ROOT/gen-out/zisk_rlp_encode_u64_${name}.expected.hex"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys, rlp
v = $v
encoded = rlp.encode(v)
with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', v))
with open(sys.argv[2], 'w') as f:
    f.write(encoded.hex())
" "$in_file" "$exp_hex_file"

  "$ZISKEMU" -e gen-out/zisk_rlp_encode_u64.elf \
    -i "$in_file" -o "$out_file" -n 100000 \
    >"$REPO_ROOT/gen-out/zisk_rlp_encode_u64_${name}.emu.log" 2>&1 || true

  local actual_status; actual_status="$(xxd -p -l 8 "$out_file" | tr -d '\n')"
  local actual_len_le; actual_len_le="$(dd if="$out_file" bs=1 skip=8 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local actual_len; actual_len="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$actual_len_le'))[0])")"
  local expected_hex; expected_hex="$(cat "$exp_hex_file")"
  local expected_len; expected_len=$(( ${#expected_hex} / 2 ))
  local actual_hex; actual_hex="$(dd if="$out_file" bs=1 skip=16 count="$expected_len" 2>/dev/null | xxd -p | tr -d '\n')"

  if [[ "$actual_status" == "0000000000000000" \
       && "$actual_len" == "$expected_len" \
       && "$actual_hex" == "$expected_hex" ]]; then
    printf "  %-30s OK   v=%s len=%d enc=%s\n" "$name" "$v" "$expected_len" "$expected_hex"
    return 0
  else
    printf "  %-30s FAIL status=0x%s actual_len=%d expected_len=%d\n" "$name" "$actual_status" "$actual_len" "$expected_len"
    printf "      actual:   %s\n" "$actual_hex"
    printf "      expected: %s\n" "$expected_hex"
    return 1
  fi
}

FAILED=0
# Single-byte form boundary cases
run_case "zero"               0          || FAILED=1
run_case "one"                1          || FAILED=1
run_case "max_single_byte"    127        || FAILED=1
# Multi-byte boundary (128 needs 0x81 0x80)
run_case "128_boundary"       128        || FAILED=1
run_case "255"                255        || FAILED=1
run_case "256_boundary"       256        || FAILED=1
# Typical values
run_case "42"                 42         || FAILED=1
run_case "10_thousand"        10000      || FAILED=1
run_case "1_million"          1000000    || FAILED=1
# Each byte-count tier
run_case "3_bytes"            65536      || FAILED=1                       # 0x010000
run_case "4_bytes"            16777216   || FAILED=1                       # 0x01000000
run_case "5_bytes"            4294967296 || FAILED=1                       # 0x0100000000
run_case "6_bytes"            1099511627776  || FAILED=1                   # 2^40
run_case "7_bytes"            281474976710656 || FAILED=1                  # 2^48
run_case "8_bytes"            72057594037927936 || FAILED=1                # 2^56
# Max u64
run_case "max_u64m1"          18446744073709551614 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: rlp_encode_u64 matches Python rlp.encode for all boundaries"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
