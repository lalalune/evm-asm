#!/usr/bin/env bash
# codegen-zisk-witness-headers-chain-link-at-index-check.sh
#
# In-witness chain-link verifier. Like #7222 but takes a
# single witness.headers section and a parent_idx, checking
# the consecutive pair (parent_idx, parent_idx+1) without
# host round-trip.
#
# Output (16 bytes):
#   bytes  0.. 8 : status (0..4)
#   bytes  8..16 : is_valid (u64; 0 or 1)
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

echo "==> emit zisk_witness_headers_chain_link_at_index ELF"
lake exe codegen --program zisk_witness_headers_chain_link_at_index \
  --halt linux93 \
  -o gen-out/zisk_witness_headers_chain_link_at_index

REPO_ROOT="$(pwd)"

run_case() {
  local name="$1"; shift
  local mode="$1"; shift
  local parent_idx="$1"; shift

  local in_file="$REPO_ROOT/gen-out/zisk_whcl_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_whcl_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_whcl_${name}.expected"

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
parent_idx = int('$parent_idx')

if mode == 'valid_chain':
    # Build h0, h1=parent_hash=keccak(h0), h2=parent_hash=keccak(h1).
    h0 = encode_header(b'\\xab' * 32)
    h1 = encode_header(k256(h0))
    h2 = encode_header(k256(h1))
    witness_headers = build_ssz_section([h0, h1, h2])
    # parent_idx valid -> is_valid=1.
    expected = struct.pack('<Q', 0) + struct.pack('<Q', 1)
elif mode == 'broken_link_at_idx':
    # Same shape but h1 doesn't reference h0.
    h0 = encode_header(b'\\xab' * 32)
    h1_bad = encode_header(b'\\xee' * 32)  # not keccak(h0)
    h2 = encode_header(k256(h1_bad))
    witness_headers = build_ssz_section([h0, h1_bad, h2])
    # parent_idx=0 -> bad link, is_valid=0.
    # parent_idx=1 -> link h1_bad to h2 IS valid.
    if parent_idx == 0:
        expected = struct.pack('<Q', 0) + struct.pack('<Q', 0)
    else:
        expected = struct.pack('<Q', 0) + struct.pack('<Q', 1)
elif mode == 'oob_parent':
    h0 = encode_header(b'\\xab' * 32)
    witness_headers = build_ssz_section([h0])
    # parent_idx out of bounds.
    expected = struct.pack('<Q', 1) + struct.pack('<Q', 0)
elif mode == 'oob_child':
    # Single header in section -> parent_idx=0 has no child at 1.
    h0 = encode_header(b'\\xab' * 32)
    witness_headers = build_ssz_section([h0])
    expected = struct.pack('<Q', 2) + struct.pack('<Q', 0)
elif mode == 'child_garbage':
    h0 = encode_header(b'\\xab' * 32)
    # second entry is too small to RLP-decode as a 15-field list.
    witness_headers = build_ssz_section([h0, b'\\x00'])
    expected = struct.pack('<Q', 3) + struct.pack('<Q', 0)
else:
    raise SystemExit('bad mode')

with open(sys.argv[1], 'wb') as f:
    record = (
        struct.pack('<Q', len(witness_headers))
        + struct.pack('<Q', parent_idx)
        + witness_headers
    )
    f.write(record)
    pad = (-len(record)) % 8
    if pad: f.write(b'\\x00' * pad)

with open(sys.argv[2], 'wb') as f:
    f.write(expected)
" "$in_file" "$exp_file"

  "$ZISKEMU" -e gen-out/zisk_witness_headers_chain_link_at_index.elf \
    -i "$in_file" -o "$out_file" -n 4000000 \
    >"$REPO_ROOT/gen-out/zisk_whcl_${name}.emu.log" 2>&1 || true

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
# 1) Valid 3-header chain, verify link 0->1.
run_case "valid_chain_idx0"            valid_chain 0 || FAILED=1
# 2) Valid 3-header chain, verify link 1->2 (exercises section_end).
run_case "valid_chain_idx1_end"        valid_chain 1 || FAILED=1
# 3) Broken link 0->1, is_valid=0.
run_case "broken_link_idx0"            broken_link_at_idx 0 || FAILED=1
# 4) Same section but link 1->2 IS valid (h2.parent_hash = keccak(h1_bad)).
run_case "intact_link_idx1_in_broken"  broken_link_at_idx 1 || FAILED=1
# 5) parent_idx OOB (only 1 header, asking parent_idx=1).
run_case "parent_idx_oob"              oob_parent 1 || FAILED=1
# 6) parent_idx=0 but no child at idx 1.
run_case "child_idx_oob"               oob_child 0 || FAILED=1
# 7) Child header bytes too small -> status 3.
run_case "child_garbage_parse_fail"    child_garbage 0 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: witness_headers_chain_link_at_index end-to-end"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
