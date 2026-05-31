#!/usr/bin/env bash
# codegen-zisk-parent-beacon-block-root-at-block-hash-check.sh
#
# Hash-keyed EIP-4788 historical header.parent_beacon_block_root
# extractor (RLP field 19, Cancun+). Mirror of the number-keyed
# `parent_beacon_block_root_at_block_number` but takes a 32-byte
# block_hash key.
#
# Output (40 bytes):
#   bytes  0.. 8 : status (0 ok, 1 hash miss, 2 RLP fail)
#   bytes  8..40 : parent_beacon_block_root (32 B; zero on failure)
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

echo "==> emit zisk_parent_beacon_block_root_at_block_hash ELF"
lake exe codegen --program zisk_parent_beacon_block_root_at_block_hash \
  --halt linux93 \
  -o gen-out/zisk_parent_beacon_block_root_at_block_hash

REPO_ROOT="$(pwd)"

run_case() {
  local name="$1"; shift
  local mode="$1"; shift

  local in_file="$REPO_ROOT/gen-out/zisk_pbrbh_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_pbrbh_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_pbrbh_${name}.expected"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys
import rlp
from Crypto.Hash import keccak

def k256(b):
    h = keccak.new(digest_bits=256); h.update(b); return h.digest()

def build_ssz_section(elements):
    n = len(elements)
    if n == 0: return b''
    section = b''
    offset = 4 * n
    for e in elements:
        section += struct.pack('<I', offset); offset += len(e)
    for e in elements: section += e
    return section

# 20-field Amsterdam header with field 19 = parent_beacon_block_root.
def encode_header(state_root, parent_beacon_block_root, n_fields=20):
    fields = [
        b'\\x11'*32, b'\\x22'*32, b'\\x33'*20, state_root, b'\\x44'*32,
        b'\\x55'*32, b'\\x00'*256, b'', b'\\x01', b'\\x83\\xff\\xff\\xff',
        b'', b'\\x83\\x01\\x02\\x03', b'', b'\\x77'*32, b'\\x00'*8,
        b'',                       # base_fee_per_gas
        b'\\x66'*32,               # withdrawals_root
        b'',                       # blob_gas_used
        b'',                       # excess_blob_gas
        parent_beacon_block_root,  # field 19
    ]
    return rlp.encode(fields[:n_fields])

mode = '$mode'

if mode == 'distinct_pbbr':
    pbbr = bytes(range(32))
    h0 = encode_header(b'\\xaa'*32, pbbr)
    witness_headers = build_ssz_section([h0])
    block_hash = k256(h0)
    expected = struct.pack('<Q', 0) + pbbr
elif mode == 'two_headers_pick_second':
    pbbr0 = b'\\x77'*32
    pbbr1 = bytes(range(31, -1, -1))
    h0 = encode_header(b'\\xaa'*32, pbbr0)
    h1 = encode_header(b'\\xbb'*32, pbbr1)
    witness_headers = build_ssz_section([h0, h1])
    block_hash = k256(h1)
    expected = struct.pack('<Q', 0) + pbbr1
elif mode == 'block_hash_miss':
    h0 = encode_header(b'\\xaa'*32, b'\\xbe'*32)
    witness_headers = build_ssz_section([h0])
    block_hash = b'\\xee'*32
    expected = struct.pack('<Q', 1) + b'\\x00'*32
elif mode == 'rlp_field_size_mismatch':
    # 33-byte field 19 forces size != 32 path
    h0 = encode_header(b'\\xaa'*32, b'\\xbb'*33)
    witness_headers = build_ssz_section([h0])
    block_hash = k256(h0)
    expected = struct.pack('<Q', 2) + b'\\x00'*32
elif mode == 'pre_cancun_field_absent':
    # 19-field (pre-Cancun-ish) header; field 19 absent entirely.
    h0 = encode_header(b'\\xaa'*32, b'\\xbb'*32, n_fields=19)
    witness_headers = build_ssz_section([h0])
    block_hash = k256(h0)
    expected = struct.pack('<Q', 2) + b'\\x00'*32
else:
    raise SystemExit('bad mode: ' + mode)

with open(sys.argv[1], 'wb') as f:
    record = (
        struct.pack('<Q', len(witness_headers))
        + block_hash
        + witness_headers
    )
    f.write(record)
    pad = (-len(record)) % 8
    if pad: f.write(b'\\x00' * pad)

with open(sys.argv[2], 'wb') as f:
    f.write(expected)
" "$in_file" "$exp_file"

  "$ZISKEMU" -e gen-out/zisk_parent_beacon_block_root_at_block_hash.elf \
    -i "$in_file" -o "$out_file" -n 6000000 \
    >"$REPO_ROOT/gen-out/zisk_pbrbh_${name}.emu.log" 2>&1 || true

  local exp_size
  exp_size="$(stat -c%s "$exp_file")"
  local actual expected
  actual="$(xxd -p -l "$exp_size" "$out_file" 2>/dev/null | tr -d '\n')"
  expected="$(xxd -p -l "$exp_size" "$exp_file" 2>/dev/null | tr -d '\n')"

  if [[ "$actual" == "$expected" ]]; then
    printf "  %-40s OK   %d bytes match\n" "$name" "$exp_size"
    return 0
  else
    printf "  %-40s FAIL\n    expected: %s\n    actual:   %s\n" \
      "$name" "$expected" "$actual"
    return 1
  fi
}

FAILED=0
run_case "distinct_pbbr"                    distinct_pbbr || FAILED=1
run_case "two_headers_pick_second"          two_headers_pick_second || FAILED=1
run_case "block_hash_miss_status_1"         block_hash_miss || FAILED=1
run_case "rlp_field_size_mismatch_status_2" rlp_field_size_mismatch || FAILED=1
run_case "pre_cancun_field_absent_status_2" pre_cancun_field_absent || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: parent_beacon_block_root_at_block_hash end-to-end"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
