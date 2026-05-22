#!/usr/bin/env bash
# codegen-zisk-tx-extract-data-section-check.sh -- PR-K104.
#
# Extract the `data` field's ptr+len from any tx type.
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

echo "==> emit zisk_tx_extract_data_section ELF"
lake exe codegen --program zisk_tx_extract_data_section --halt linux93 \
  -o gen-out/zisk_tx_extract_data_section

REPO_ROOT="$(pwd)"

# run_case <name> <tx_type> <data_hex>
run_case() {
  local name="$1" t="$2" data_hex="$3"

  local in_file="$REPO_ROOT/gen-out/zisk_tx_extract_data_section_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_tx_extract_data_section_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys, rlp
tx_type = '$t'
data = bytes.fromhex('$data_hex')
ALICE = bytes([0xaa]*20)
R = int.from_bytes(bytes([0x11]*32), 'big')
S = int.from_bytes(bytes([0x22]*32), 'big')

if tx_type == 'legacy':
    tx = [1, 10**9, 21000, ALICE, 10**18, data, 27, R, S]
    tx_bytes = rlp.encode(tx)
elif tx_type == 'eip2930':
    inner = [1, 7, 10**9, 21000, ALICE, 10**18, data, [], 1, R, S]
    tx_bytes = b'\x01' + rlp.encode(inner)
elif tx_type == 'eip1559':
    inner = [1, 7, 10**9, 2*10**9, 21000, ALICE, 10**18, data, [], 1, R, S]
    tx_bytes = b'\x02' + rlp.encode(inner)
elif tx_type == 'eip4844':
    H = bytes([0x01] + [0xab]*31)
    inner = [
        1, 7, 10**9, 2*10**9, 21000,
        ALICE, 10**18, data, [],
        1, [H], 0, R, S,
    ]
    tx_bytes = b'\x03' + rlp.encode(inner)
elif tx_type == 'eip7702':
    auth_list = [[1, ALICE, 0, 27, R, S]]
    inner = [1, 7, 10**9, 2*10**9, 21000, ALICE, 10**18, data, [], auth_list, 1, R, S]
    tx_bytes = b'\x04' + rlp.encode(inner)
else:
    raise ValueError(tx_type)

with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(tx_bytes)))
    f.write(tx_bytes)
    pad = (-(8 + len(tx_bytes))) % 8
    if pad: f.write(b'\x00' * pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_tx_extract_data_section.elf \
    -i "$in_file" -o "$out_file" -n 1000000 \
    >"$REPO_ROOT/gen-out/zisk_tx_extract_data_section_${name}.emu.log" 2>&1 || true

  local actual_status; actual_status="$(xxd -p -l 8 "$out_file" | tr -d '\n')"
  local actual_ptr_le; actual_ptr_le="$(dd if="$out_file" bs=1 skip=8 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local actual_len_le; actual_len_le="$(dd if="$out_file" bs=1 skip=16 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  # Decode pointer to little-endian integer
  local actual_ptr_dec; actual_ptr_dec="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$actual_ptr_le'))[0])")"
  local actual_len_dec; actual_len_dec="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$actual_len_le'))[0])")"
  local expected_len; expected_len="$(python3 -c "print(len(bytes.fromhex('$data_hex')))")"

  if [[ "$actual_status" != "0000000000000000" ]]; then
    printf "  %-32s FAIL  status=0x%s\n" "$name" "$actual_status"
    return 1
  fi
  if [[ "$actual_len_dec" != "$expected_len" ]]; then
    printf "  %-32s FAIL  data_len=%d expected=%d\n" "$name" "$actual_len_dec" "$expected_len"
    return 1
  fi
  # Cross-verify: read data bytes from the pointer and check they match.
  # The probe loads tx_bytes at INPUT+16 (0x40000010). Compute expected pointer
  # offset within the input file and verify by reading the input file.
  local input_offset=$((actual_ptr_dec - 0x40000010 + 8))
  local actual_data_hex
  if [[ "$expected_len" == "0" ]]; then
    actual_data_hex=""
  else
    actual_data_hex="$(dd if="$in_file" bs=1 skip="$input_offset" count="$expected_len" 2>/dev/null | xxd -p | tr -d '\n')"
  fi
  if [[ "$actual_data_hex" == "$data_hex" ]]; then
    printf "  %-32s OK   ptr=0x%x len=%d\n" "$name" "$actual_ptr_dec" "$expected_len"
    return 0
  else
    printf "  %-32s FAIL  ptr=0x%x data mismatch\n    expected: %s\n    actual:   %s\n" "$name" "$actual_ptr_dec" "${data_hex:0:32}" "${actual_data_hex:0:32}"
    return 1
  fi
}

FAILED=0
run_case "legacy_empty"      legacy   ""                                             || FAILED=1
run_case "legacy_4bytes"     legacy   "deadbeef"                                     || FAILED=1
run_case "legacy_long"       legacy   "$(python3 -c "print('aa' * 200)")"            || FAILED=1
run_case "eip2930_empty"     eip2930  ""                                             || FAILED=1
run_case "eip1559_calldata"  eip1559  "a9059cbb000000000000000000000000aaaa"          || FAILED=1
run_case "eip4844_short"     eip4844  "0011"                                         || FAILED=1
run_case "eip7702_data"      eip7702  "$(python3 -c "print('ff' * 64)")"             || FAILED=1
run_case "legacy_init_code"  legacy   "6080604052348015600f57600080fd5b50603f80601d6000396000f3fe" || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: tx_extract_data_section returns (ptr, len) for data field across all tx types"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
