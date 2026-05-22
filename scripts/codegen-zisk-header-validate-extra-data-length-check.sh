#!/usr/bin/env bash
# codegen-zisk-header-validate-extra-data-length-check.sh -- PR-K68.
#
# Verify header.extra_data <= 32 bytes per Ethereum spec.
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

echo "==> emit zisk_header_validate_extra_data_length ELF"
lake exe codegen --program zisk_header_validate_extra_data_length --halt linux93 \
  -o gen-out/zisk_header_validate_extra_data_length

REPO_ROOT="$(pwd)"

build_header() {
  local extra_data_hex="$1"
  uv run --directory execution-specs --quiet python3 -c "
import sys
import rlp
extra = bytes.fromhex('$extra_data_hex')
fields = [
    b'\x11' * 32, b'\x22' * 32, b'\x33' * 20, b'\x44' * 32,
    b'\x55' * 32, b'\x66' * 32, b'\x00' * 256, 0,
    100, 0x1c9c380, 0x100, 1700000000,
    extra,                # 12: extra_data (variable)
    b'\x77' * 32,         # 13: prev_randao
    b'\x00' * 8,          # 14: nonce
]
sys.stdout.buffer.write(rlp.encode(fields))
"
}

# run_case <name> <expected_status> <extra_data_hex>
run_case() {
  local name="$1" expected_status="$2" extra_hex="$3"

  local header_file="$REPO_ROOT/gen-out/zisk_header_validate_extra_data_length_${name}.header"
  local in_file="$REPO_ROOT/gen-out/zisk_header_validate_extra_data_length_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_header_validate_extra_data_length_${name}.output"

  build_header "$extra_hex" > "$header_file"
  python3 -c "
import struct, sys
with open(sys.argv[1], 'rb') as f:
    body = f.read()
out  = struct.pack('<Q', len(body))
out += body
pad = (-(8 + len(body))) % 8
if pad:
    out += b'\x00' * pad
sys.stdout.buffer.write(out)
" "$header_file" > "$in_file"

  "$ZISKEMU" -e gen-out/zisk_header_validate_extra_data_length.elf \
    -i "$in_file" -o "$out_file" -n 500000 \
    >"$REPO_ROOT/gen-out/zisk_header_validate_extra_data_length_${name}.emu.log" 2>&1 || true

  local actual; actual="$(xxd -p -l 8 "$out_file" | tr -d '\n')"
  local exp_le; exp_le="$(python3 -c "print(int('$expected_status').to_bytes(8, 'little').hex())")"

  if [[ "$actual" == "$exp_le" ]]; then
    printf "  %-30s OK   status=%d (extra_len=%d)\n" "$name" "$expected_status" "$((${#extra_hex} / 2))"
    return 0
  else
    printf "  %-30s FAIL  expected status=%d got 0x%s\n" "$name" "$expected_status" "$actual"
    return 1
  fi
}

FAILED=0
# Pass cases (len ≤ 32)
run_case "empty_extra"         0 ""                                                || FAILED=1
run_case "one_byte"            0 "ff"                                              || FAILED=1
run_case "4_bytes"             0 "74657374"                                         || FAILED=1  # b'test'
run_case "31_bytes"            0 "$(printf 'aa%.0s' $(seq 1 31))"                  || FAILED=1
run_case "32_bytes_max"        0 "$(printf 'aa%.0s' $(seq 1 32))"                  || FAILED=1
run_case "32_zero_bytes"       0 "$(printf '00%.0s' $(seq 1 32))"                  || FAILED=1
# Reject cases (len > 32)
run_case "33_bytes"            1 "$(printf 'bb%.0s' $(seq 1 33))"                  || FAILED=1
run_case "64_bytes"            1 "$(printf 'cc%.0s' $(seq 1 64))"                  || FAILED=1
run_case "100_bytes"           1 "$(printf 'dd%.0s' $(seq 1 100))"                 || FAILED=1
# 200 bytes — triggers long-string RLP prefix path
run_case "200_bytes_long_rlp"  1 "$(printf 'ee%.0s' $(seq 1 200))"                 || FAILED=1

# Non-list input (parse fail)
NON_LIST_FILE="$REPO_ROOT/gen-out/zisk_header_validate_extra_data_length_non_list.input"
python3 -c "
import struct, sys
b = bytes([0x80])
with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(b)))
    f.write(b)
    f.write(b'\x00' * 7)
" "$NON_LIST_FILE"
"$ZISKEMU" -e gen-out/zisk_header_validate_extra_data_length.elf \
  -i "$NON_LIST_FILE" -o "$REPO_ROOT/gen-out/zisk_header_validate_extra_data_length_non_list.output" \
  -n 500000 >"$REPO_ROOT/gen-out/zisk_header_validate_extra_data_length_non_list.emu.log" 2>&1 || true
NL_STATUS="$(xxd -p -l 8 "$REPO_ROOT/gen-out/zisk_header_validate_extra_data_length_non_list.output" | tr -d '\n')"
if [[ "$NL_STATUS" == "0200000000000000" ]]; then
  printf "  %-30s OK   status=2 (parse fail)\n" "non_list_parse_fail"
else
  printf "  %-30s FAIL  status=0x%s\n" "non_list_parse_fail" "$NL_STATUS"
  FAILED=1
fi

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: header_validate_extra_data_length enforces ≤ 32-byte limit"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
