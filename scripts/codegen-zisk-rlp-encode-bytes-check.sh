#!/usr/bin/env bash
# codegen-zisk-rlp-encode-bytes-check.sh -- PR-K128.
#
# Generic RLP byte-string encoder.
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

echo "==> emit zisk_rlp_encode_bytes ELF"
lake exe codegen --program zisk_rlp_encode_bytes --halt linux93 \
  -o gen-out/zisk_rlp_encode_bytes

REPO_ROOT="$(pwd)"

# run_case <name> <data_hex>
run_case() {
  local name="$1" data="$2"

  local in_file="$REPO_ROOT/gen-out/zisk_rlp_encode_bytes_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_rlp_encode_bytes_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys, rlp
data = bytes.fromhex('$data')
expected = rlp.encode(data)
with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(data)))
    f.write(data)
    pad = (-(8 + len(data))) % 8
    if pad: f.write(b'\x00' * pad)
with open(sys.argv[1] + '.expected', 'wb') as f:
    f.write(struct.pack('<Q', len(expected)))
    f.write(expected)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_rlp_encode_bytes.elf \
    -i "$in_file" -o "$out_file" -n 5000000 \
    >"$REPO_ROOT/gen-out/zisk_rlp_encode_bytes_${name}.emu.log" 2>&1 || true

  local actual_status; actual_status="$(xxd -p -l 8 "$out_file" | tr -d '\n')"
  local actual_len_le; actual_len_le="$(dd if="$out_file" bs=1 skip=8 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local actual_len; actual_len="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$actual_len_le'))[0])")"
  local expected_len_le; expected_len_le="$(dd if="$in_file.expected" bs=1 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local expected_len; expected_len="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$expected_len_le'))[0])")"

  if [[ "$actual_status" != "0000000000000000" ]]; then
    printf "  %-32s FAIL status=0x%s\n" "$name" "$actual_status"
    return 1
  fi
  if [[ "$actual_len" != "$expected_len" ]]; then
    printf "  %-32s FAIL len=%d expected=%d\n" "$name" "$actual_len" "$expected_len"
    return 1
  fi
  local actual_bytes; actual_bytes="$(dd if="$out_file" bs=1 skip=16 count="$actual_len" 2>/dev/null | xxd -p | tr -d '\n')"
  local expected_bytes; expected_bytes="$(dd if="$in_file.expected" bs=1 skip=8 count="$expected_len" 2>/dev/null | xxd -p | tr -d '\n')"
  if [[ "$actual_bytes" == "$expected_bytes" ]]; then
    printf "  %-32s OK   len=%d\n" "$name" "$actual_len"
    return 0
  else
    printf "  %-32s FAIL\n    expected: %s\n    actual:   %s\n" "$name" "${expected_bytes:0:64}" "${actual_bytes:0:64}"
    return 1
  fi
}

FAILED=0
# Single-byte branch (byte < 0x80)
run_case "empty"                ""                                              || FAILED=1
run_case "byte_zero"            "00"                                            || FAILED=1
run_case "byte_7f"              "7f"                                            || FAILED=1
# Single byte ≥ 0x80 → short string
run_case "byte_80"              "80"                                            || FAILED=1
run_case "byte_ff"              "ff"                                            || FAILED=1
# Short-string (< 56 bytes)
run_case "two_bytes"            "deadbeef"                                      || FAILED=1
run_case "thirteen_bytes"       "00112233445566778899aabbcc"                    || FAILED=1
run_case "fifty_five_bytes"     "$(python3 -c "print('aa' * 55)")"              || FAILED=1
# Long-string boundary
run_case "fifty_six_bytes"      "$(python3 -c "print('bb' * 56)")"              || FAILED=1
run_case "two_hundred"          "$(python3 -c "print('cc' * 200)")"             || FAILED=1
# 2-byte length (capped to fit 256-byte output dump: 16 header + 3 prefix + N data <= 256)
run_case "len_230_2byte_prefix" "$(python3 -c "print('dd' * 230)")"             || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: rlp_encode_bytes matches Python rlp.encode"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
