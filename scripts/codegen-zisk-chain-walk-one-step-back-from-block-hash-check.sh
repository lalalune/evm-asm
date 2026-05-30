#!/usr/bin/env bash
# codegen-zisk-chain-walk-one-step-back-from-block-hash-check.sh
#
# One-step backward chain walk. Find current header by
# block_hash, extract parent_hash, check if parent is in
# witness.headers.
#
# Output (48 bytes):
#   bytes  0.. 8 : status (0..3)
#   bytes  8..40 : parent_hash (32 B)
#   bytes 40..48 : parent_in_witness (u64; 0 or 1)
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

echo "==> emit zisk_chain_walk_one_step_back_from_block_hash ELF"
lake exe codegen --program zisk_chain_walk_one_step_back_from_block_hash \
  --halt linux93 \
  -o gen-out/zisk_chain_walk_one_step_back_from_block_hash

REPO_ROOT="$(pwd)"

run_case() {
  local name="$1"; shift
  local mode="$1"; shift

  local in_file="$REPO_ROOT/gen-out/zisk_cwosb_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_cwosb_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_cwosb_${name}.expected"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys
import rlp
from Crypto.Hash import keccak

def k256(b):
    h = keccak.new(digest_bits=256); h.update(b); return h.digest()

def encode_header(parent_hash):
    fields = [
        parent_hash, b'\\x22'*32, b'\\x33'*20, b'\\x44'*32, b'\\x55'*32,
        b'\\x66'*32, b'\\x00'*256, b'', b'\\x01', b'\\x83\\xff\\xff\\xff',
        b'', b'\\x83\\x01\\x02\\x03', b'', b'\\x77'*32, b'\\x00'*8,
    ]
    return rlp.encode(fields)

def build_ssz_section(elements):
    n = len(elements)
    if n == 0: return b''
    section = b''
    offset = 4 * n
    for e in elements:
        section += struct.pack('<I', offset); offset += len(e)
    for e in elements: section += e
    return section

mode = '$mode'

if mode == 'parent_present':
    # h0 -> h1 (parent: h0).
    h0 = encode_header(b'\\xab' * 32)
    h1 = encode_header(k256(h0))
    witness_headers = build_ssz_section([h0, h1])
    current = k256(h1)  # walk from h1
    parent_hash = k256(h0)
    expected = (
        struct.pack('<Q', 0)
        + parent_hash
        + struct.pack('<Q', 1)
    )
elif mode == 'parent_missing':
    # h0 in witness but its parent (b'\\xab'*32) is NOT a witness header.
    h0 = encode_header(b'\\xab' * 32)
    witness_headers = build_ssz_section([h0])
    current = k256(h0)
    parent_hash = b'\\xab' * 32  # the parent of h0, not in witness
    expected = (
        struct.pack('<Q', 0)
        + parent_hash
        + struct.pack('<Q', 0)
    )
elif mode == 'current_not_in_witness':
    h0 = encode_header(b'\\xab' * 32)
    witness_headers = build_ssz_section([h0])
    current = b'\\xee' * 32  # unrelated hash
    expected = (
        struct.pack('<Q', 1)
        + b'\\x00' * 32
        + struct.pack('<Q', 0)
    )
else:
    raise SystemExit('bad mode')

with open(sys.argv[1], 'wb') as f:
    record = (
        struct.pack('<Q', len(witness_headers))
        + current
        + witness_headers
    )
    f.write(record)
    pad = (-len(record)) % 8
    if pad: f.write(b'\\x00' * pad)

with open(sys.argv[2], 'wb') as f:
    f.write(expected)
" "$in_file" "$exp_file"

  "$ZISKEMU" -e gen-out/zisk_chain_walk_one_step_back_from_block_hash.elf \
    -i "$in_file" -o "$out_file" -n 4000000 \
    >"$REPO_ROOT/gen-out/zisk_cwosb_${name}.emu.log" 2>&1 || true

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
run_case "parent_present_in_witness"      parent_present || FAILED=1
run_case "parent_missing_from_witness"    parent_missing || FAILED=1
run_case "current_not_in_witness"         current_not_in_witness || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: chain_walk_one_step_back_from_block_hash end-to-end"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
