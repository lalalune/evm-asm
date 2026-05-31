#!/usr/bin/env bash
# codegen-zisk-receipts-root-at-block-hash-check.sh
#
# Hash-keyed historical header.receipts_root extractor.
# Mirror of the number-keyed `receipts_root_at_block_number`
# but takes a 32-byte block_hash key.
#
# Output (40 bytes):
#   bytes  0.. 8 : status (0 ok, 1 hash miss, 2 RLP fail)
#   bytes  8..40 : receipts_root (32 B; zero on failure)
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

echo "==> emit zisk_receipts_root_at_block_hash ELF"
lake exe codegen --program zisk_receipts_root_at_block_hash \
  --halt linux93 \
  -o gen-out/zisk_receipts_root_at_block_hash

REPO_ROOT="$(pwd)"

run_case() {
  local name="$1"; shift
  local mode="$1"; shift

  local in_file="$REPO_ROOT/gen-out/zisk_rrbh_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_rrbh_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_rrbh_${name}.expected"

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

def encode_header(state_root, receipts_root):
    fields = [
        b'\\x11'*32, b'\\x22'*32, b'\\x33'*20, state_root, b'\\x44'*32,
        receipts_root, b'\\x00'*256, b'', b'\\x01', b'\\x83\\xff\\xff\\xff',
        b'', b'\\x83\\x01\\x02\\x03', b'', b'\\x77'*32, b'\\x00'*8,
        b'', b'\\x88'*32, b'', b'', b'\\x99'*32,
    ]
    return rlp.encode(fields)

def encode_header_with_rr(state_root, receipts_root_bytes):
    fields = [
        b'\\x11'*32, b'\\x22'*32, b'\\x33'*20, state_root, b'\\x44'*32,
        receipts_root_bytes, b'\\x00'*256, b'', b'\\x01', b'\\x83\\xff\\xff\\xff',
        b'', b'\\x83\\x01\\x02\\x03', b'', b'\\x77'*32, b'\\x00'*8,
        b'', b'\\x88'*32, b'', b'', b'\\x99'*32,
    ]
    return rlp.encode(fields)

mode = '$mode'

if mode == 'distinct_receipts_root':
    rr = bytes(range(32))
    h0 = encode_header(b'\\xaa'*32, rr)
    witness_headers = build_ssz_section([h0])
    block_hash = k256(h0)
    expected = struct.pack('<Q', 0) + rr
elif mode == 'three_headers_pick_middle':
    rr0 = b'\\x77'*32
    rr1 = bytes(range(31, -1, -1))
    rr2 = b'\\xee'*32
    h0 = encode_header(b'\\xaa'*32, rr0)
    h1 = encode_header(b'\\xbb'*32, rr1)
    h2 = encode_header(b'\\xcc'*32, rr2)
    witness_headers = build_ssz_section([h0, h1, h2])
    block_hash = k256(h1)
    expected = struct.pack('<Q', 0) + rr1
elif mode == 'block_hash_miss':
    h0 = encode_header(b'\\xaa'*32, b'\\x12'*32)
    witness_headers = build_ssz_section([h0])
    block_hash = b'\\xee'*32
    expected = struct.pack('<Q', 1) + b'\\x00'*32
elif mode == 'rlp_field_size_mismatch':
    # 33-byte receipts_root forces field-5-size != 32 path
    h0 = encode_header_with_rr(b'\\xaa'*32, b'\\x77'*33)
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

  "$ZISKEMU" -e gen-out/zisk_receipts_root_at_block_hash.elf \
    -i "$in_file" -o "$out_file" -n 6000000 \
    >"$REPO_ROOT/gen-out/zisk_rrbh_${name}.emu.log" 2>&1 || true

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
run_case "distinct_receipts_root"           distinct_receipts_root || FAILED=1
run_case "three_headers_pick_middle"        three_headers_pick_middle || FAILED=1
run_case "block_hash_miss_status_1"         block_hash_miss || FAILED=1
run_case "rlp_field_size_mismatch_status_2" rlp_field_size_mismatch || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: receipts_root_at_block_hash end-to-end"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
