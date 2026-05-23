#!/usr/bin/env bash
# codegen-zisk-rlp-encode-list-prefix-check.sh -- PR-K129.
#
# RLP list-header prefix encoder.
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

echo "==> emit zisk_rlp_encode_list_prefix ELF"
lake exe codegen --program zisk_rlp_encode_list_prefix --halt linux93 \
  -o gen-out/zisk_rlp_encode_list_prefix

REPO_ROOT="$(pwd)"

# run_case <name> <payload_length>
run_case() {
  local name="$1" plen="$2"

  local in_file="$REPO_ROOT/gen-out/zisk_rlp_encode_list_prefix_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_rlp_encode_list_prefix_${name}.output"

  python3 -c "
import struct, sys
plen = $plen
if plen < 56:
    expected = bytes([0xc0 + plen])
else:
    # Compute byte count
    bc = (plen.bit_length() + 7) // 8
    expected = bytes([0xf7 + bc]) + plen.to_bytes(bc, 'big')

with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', plen))
with open(sys.argv[1] + '.expected', 'wb') as f:
    f.write(struct.pack('<Q', len(expected)))
    f.write(expected)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_rlp_encode_list_prefix.elf \
    -i "$in_file" -o "$out_file" -n 1000000 \
    >"$REPO_ROOT/gen-out/zisk_rlp_encode_list_prefix_${name}.emu.log" 2>&1 || true

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
    printf "  %-32s OK   plen=%d → %s\n" "$name" "$plen" "$expected_bytes"
    return 0
  else
    printf "  %-32s FAIL\n    expected: %s\n    actual:   %s\n" "$name" "$expected_bytes" "$actual_bytes"
    return 1
  fi
}

FAILED=0
# Short list (0..55)
run_case "empty_list"             0     || FAILED=1
run_case "len_1"                  1     || FAILED=1
run_case "len_22"                 22    || FAILED=1
run_case "len_55"                 55    || FAILED=1
# Long list - 1 byte length
run_case "len_56"                 56    || FAILED=1
run_case "len_127"                127   || FAILED=1
run_case "len_255"                255   || FAILED=1
# 2-byte length
run_case "len_256"                256   || FAILED=1
run_case "len_65535"              65535 || FAILED=1
# 3-byte length
run_case "len_65536"              65536 || FAILED=1
run_case "len_one_million"        1000000 || FAILED=1
# 4..8 byte lengths
run_case "len_u32_max"            "$((1 << 32 - 1))" || FAILED=1
run_case "len_u48"                "$((1 << 40))" || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: rlp_encode_list_prefix matches RLP list-header rule"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
