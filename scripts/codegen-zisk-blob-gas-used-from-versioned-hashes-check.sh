#!/usr/bin/env bash
# codegen-zisk-blob-gas-used-from-versioned-hashes-check.sh -- PR-K64.
#
# Compute EIP-4844 blob_gas_used = count(blob_versioned_hashes) × GAS_PER_BLOB.
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

echo "==> emit zisk_blob_gas_used_from_versioned_hashes ELF"
lake exe codegen --program zisk_blob_gas_used_from_versioned_hashes --halt linux93 \
  -o gen-out/zisk_blob_gas_used_from_versioned_hashes

REPO_ROOT="$(pwd)"

# run_case <name> <expected_status> <gas_per_blob> <num_hashes>
run_case() {
  local name="$1" expected_status="$2" gas_per_blob="$3" num_hashes="$4"

  local in_file="$REPO_ROOT/gen-out/zisk_blob_gas_used_from_versioned_hashes_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_blob_gas_used_from_versioned_hashes_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys
import rlp

n = $num_hashes
# Make each hash distinct enough to exercise the byte-walk
hashes = [
    bytes([0x01] + [(i*7+3) & 0xff for _ in range(31)]) for i in range(n)
]
list_rlp = rlp.encode(hashes)

with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(list_rlp)))
    f.write(struct.pack('<Q', $gas_per_blob))
    f.write(list_rlp)
    pad = (-(16 + len(list_rlp))) % 8
    if pad:
        f.write(b'\x00' * pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_blob_gas_used_from_versioned_hashes.elf \
    -i "$in_file" -o "$out_file" -n 500000 \
    >"$REPO_ROOT/gen-out/zisk_blob_gas_used_from_versioned_hashes_${name}.emu.log" 2>&1 || true

  local actual_status; actual_status="$(xxd -p -l 8 "$out_file" | tr -d '\n')"
  local actual_result; actual_result="$(dd if="$out_file" bs=1 skip=8 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local expected_result; expected_result="$(python3 -c "print($num_hashes * $gas_per_blob)")"

  local exp_status_le; exp_status_le="$(python3 -c "print(int('$expected_status').to_bytes(8, 'little').hex())")"
  local exp_result_le; exp_result_le="$(python3 -c "print(int('$expected_result').to_bytes(8, 'little').hex())")"

  if [[ "$actual_status" == "$exp_status_le" && "$actual_result" == "$exp_result_le" ]]; then
    printf "  %-30s OK   status=%d blob_gas_used=%d\n" "$name" "$expected_status" "$expected_result"
    return 0
  else
    printf "  %-30s FAIL  expected status=%d result=%d got status=0x%s result=0x%s\n" \
      "$name" "$expected_status" "$expected_result" "$actual_status" "$actual_result"
    return 1
  fi
}

GAS_PER_BLOB=131072

FAILED=0
# Edge cases
run_case "empty_list"            0 "$GAS_PER_BLOB" 0  || FAILED=1
run_case "one_blob"              0 "$GAS_PER_BLOB" 1  || FAILED=1
run_case "two_blobs"             0 "$GAS_PER_BLOB" 2  || FAILED=1
run_case "three_blobs_target"    0 "$GAS_PER_BLOB" 3  || FAILED=1
# Cancun cap (6 blobs/tx)
run_case "six_blobs_cancun_max"  0 "$GAS_PER_BLOB" 6  || FAILED=1
# Prague-era max (9 blobs/tx)
run_case "nine_blobs_prague"     0 "$GAS_PER_BLOB" 9  || FAILED=1
# Hypothetical 16 blobs (stress test for long RLP prefix path)
run_case "sixteen_blobs"         0 "$GAS_PER_BLOB" 16 || FAILED=1
# Different gas_per_blob values (test the multiplication)
run_case "one_blob_small_gas"    0 100             1  || FAILED=1
run_case "three_blobs_big_gas"   0 1000000         3  || FAILED=1
# Non-list input → status=1
NON_LIST_FILE="$REPO_ROOT/gen-out/zisk_blob_gas_used_from_versioned_hashes_non_list.input"
python3 -c "
import struct, sys
b = bytes([0x80])  # RLP empty string, not a list
with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(b)))
    f.write(struct.pack('<Q', 131072))  # gas_per_blob
    f.write(b)
    f.write(b'\x00' * 7)
" "$NON_LIST_FILE"
"$ZISKEMU" -e gen-out/zisk_blob_gas_used_from_versioned_hashes.elf \
  -i "$NON_LIST_FILE" -o "$REPO_ROOT/gen-out/zisk_blob_gas_used_from_versioned_hashes_non_list.output" \
  -n 500000 >"$REPO_ROOT/gen-out/zisk_blob_gas_used_from_versioned_hashes_non_list.emu.log" 2>&1 || true
NL_STATUS="$(xxd -p -l 8 "$REPO_ROOT/gen-out/zisk_blob_gas_used_from_versioned_hashes_non_list.output" | tr -d '\n')"
NL_RESULT="$(dd if="$REPO_ROOT/gen-out/zisk_blob_gas_used_from_versioned_hashes_non_list.output" bs=1 skip=8 count=8 2>/dev/null | xxd -p | tr -d '\n')"
if [[ "$NL_STATUS" == "0100000000000000" && "$NL_RESULT" == "0000000000000000" ]]; then
  printf "  %-30s OK   status=1 (non-list rejected)\n" "non_list_rejected"
else
  printf "  %-30s FAIL  status=0x%s result=0x%s\n" "non_list_rejected" "$NL_STATUS" "$NL_RESULT"
  FAILED=1
fi

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: blob_gas_used_from_versioned_hashes returns count × gas_per_blob"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
