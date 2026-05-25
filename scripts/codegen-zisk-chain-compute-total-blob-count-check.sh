#!/usr/bin/env bash
# codegen-zisk-chain-compute-total-blob-count-check.sh -- PR-K248.
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

echo "==> emit zisk_chain_compute_total_blob_count ELF"
lake exe codegen --program zisk_chain_compute_total_blob_count --halt linux93 \
  -o gen-out/zisk_chain_compute_total_blob_count

REPO_ROOT="$(pwd)"

run_case() {
  local name="$1" blobs_per_block="$2" exp_status="$3" exp_count="$4"

  local in_file="$REPO_ROOT/gen-out/zisk_chain_compute_total_blob_count_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_chain_compute_total_blob_count_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys, rlp
def u_be(n):
    if n == 0: return b''
    return n.to_bytes((n.bit_length() + 7) // 8, 'big')

GAS_PER_BLOB = 131072
def make_header_cancun(n_blobs):
    blob_gas = n_blobs * GAS_PER_BLOB
    return rlp.encode([
        b'\\xa1'*32, b'\\xa2'*32, b'\\xa3'*20, b'\\xa4'*32, b'\\xa5'*32,
        b'\\xa6'*32, b'\\x00'*256, b'', b'\\x01', b'\\x83\\xff\\xff\\xff',
        b'', b'\\x83\\x01\\x02\\x03', b'', b'\\xa7'*32, b'\\x00'*8,
        b'\\x82\\x01\\x00', b'\\xa8'*32,
        u_be(blob_gas),
        u_be(0),
    ])

blobs = $blobs_per_block
headers = [make_header_cancun(n) for n in blobs]
N = len(headers)
lengths = b''.join(struct.pack('<Q', len(h)) for h in headers)
flat = b''.join(headers)
with open(sys.argv[1], 'wb') as f:
    record = struct.pack('<Q', N) + lengths + flat
    f.write(record)
    pad = (-len(record)) % 8
    if pad: f.write(b'\x00' * pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_chain_compute_total_blob_count.elf \
    -i "$in_file" -o "$out_file" -n 5000000 \
    >"$REPO_ROOT/gen-out/zisk_chain_compute_total_blob_count_${name}.emu.log" 2>&1 || true

  local s_le; s_le="$(dd if="$out_file" bs=1 skip=8  count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local c_le; c_le="$(dd if="$out_file" bs=1 skip=16 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local status count
  status="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$s_le'))[0])")"
  count="$( python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$c_le'))[0])")"

  if [[ "$status" == "$exp_status" && "$count" == "$exp_count" ]]; then
    printf "  %-26s OK   status=%s count=%s\n" "$name" "$status" "$count"
    return 0
  else
    printf "  %-26s FAIL status=%s/%s count=%s/%s\n" "$name" "$status" "$exp_status" "$count" "$exp_count"
    return 1
  fi
}

FAILED=0
run_case "empty"           "[]"          0 0     || FAILED=1
run_case "single_zero"     "[0]"         0 0     || FAILED=1
run_case "single_one_blob" "[1]"         0 1     || FAILED=1
run_case "single_six"      "[6]"         0 6     || FAILED=1
run_case "three_mixed"     "[1,2,3]"     0 6     || FAILED=1
run_case "three_max"       "[6,6,6]"     0 18    || FAILED=1
run_case "all_empty_blocks" "[0,0,0,0]"  0 0     || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: chain_compute_total_blob_count sums blob_gas_used / GAS_PER_BLOB across N"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
