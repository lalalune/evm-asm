#!/usr/bin/env bash
# codegen-zisk-post-merge-invariants-at-block-hash-check.sh
#
# Hash-keyed EIP-3675 post-merge invariant canary. Mirrors
# the Python `validate_header` block:
#   assert header.ommers_hash == EMPTY_OMMERS_HASH
#   assert header.difficulty == 0
#   assert header.nonce      == b'\x00' * 8
# but takes a 32-byte block_hash instead of a raw header
# buffer.  One-shot Boolean canary.
#
# Output (8 bytes):
#   bytes 0..8 : status (0..5)
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

echo "==> emit zisk_post_merge_invariants_at_block_hash ELF"
lake exe codegen --program zisk_post_merge_invariants_at_block_hash \
  --halt linux93 \
  -o gen-out/zisk_post_merge_invariants_at_block_hash

REPO_ROOT="$(pwd)"

run_case() {
  local name="$1"; shift
  local mode="$1"; shift

  local in_file="$REPO_ROOT/gen-out/zisk_pmibh_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_pmibh_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_pmibh_${name}.expected"

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

def be_min(val):
    if val == 0: return b''
    nbytes = (val.bit_length() + 7) // 8
    return val.to_bytes(nbytes, 'big')

EMPTY_OMMERS_HASH = bytes.fromhex(
    '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347'
)

def encode_header(ommers_hash, difficulty_val, nonce_bytes):
    fields = [
        b'\\x11'*32, ommers_hash, b'\\x33'*20, b'\\xaa'*32, b'\\x44'*32,
        b'\\x55'*32, b'\\x00'*256, be_min(difficulty_val), b'\\x01',
        b'\\x83\\xff\\xff\\xff',
        b'', b'\\x83\\x01\\x02\\x03', b'', b'\\x77'*32, nonce_bytes,
        b'', b'\\x66'*32, b'', b'', b'\\x99'*32,
    ]
    return rlp.encode(fields)

def encode_header_short(ommers_hash, difficulty_val, nonce_bytes):
    # 14-field header (lacks field 14 = nonce). Forces parse_fail
    # in the K67 validator.
    fields = [
        b'\\x11'*32, ommers_hash, b'\\x33'*20, b'\\xaa'*32, b'\\x44'*32,
        b'\\x55'*32, b'\\x00'*256, be_min(difficulty_val), b'\\x01',
        b'\\x83\\xff\\xff\\xff',
        b'', b'\\x83\\x01\\x02\\x03', b'', b'\\x77'*32,
    ]
    return rlp.encode(fields)

mode = '$mode'

if mode == 'canonical_post_merge':
    h0 = encode_header(EMPTY_OMMERS_HASH, 0, b'\\x00'*8)
    witness_headers = build_ssz_section([h0])
    block_hash = k256(h0)
    expected = struct.pack('<Q', 0)
elif mode == 'ommers_hash_mismatch':
    h0 = encode_header(b'\\xab'*32, 0, b'\\x00'*8)
    witness_headers = build_ssz_section([h0])
    block_hash = k256(h0)
    expected = struct.pack('<Q', 2)
elif mode == 'difficulty_nonzero':
    h0 = encode_header(EMPTY_OMMERS_HASH, 1, b'\\x00'*8)
    witness_headers = build_ssz_section([h0])
    block_hash = k256(h0)
    expected = struct.pack('<Q', 3)
elif mode == 'difficulty_large_pow':
    h0 = encode_header(EMPTY_OMMERS_HASH, 12345678901234567890, b'\\x00'*8)
    witness_headers = build_ssz_section([h0])
    block_hash = k256(h0)
    expected = struct.pack('<Q', 3)
elif mode == 'nonce_nonzero':
    h0 = encode_header(EMPTY_OMMERS_HASH, 0,
                       b'\\xCA\\xFE\\xBA\\xBE\\xDE\\xAD\\xBE\\xEF')
    witness_headers = build_ssz_section([h0])
    block_hash = k256(h0)
    expected = struct.pack('<Q', 4)
elif mode == 'rlp_field_14_missing':
    h0 = encode_header_short(EMPTY_OMMERS_HASH, 0, b'\\x00'*8)
    witness_headers = build_ssz_section([h0])
    block_hash = k256(h0)
    expected = struct.pack('<Q', 5)
elif mode == 'two_headers_pick_second_canonical':
    h0 = encode_header(b'\\xab'*32, 99, b'\\xff'*8)  # invalid h0
    h1 = encode_header(EMPTY_OMMERS_HASH, 0, b'\\x00'*8)  # canonical h1
    witness_headers = build_ssz_section([h0, h1])
    block_hash = k256(h1)
    expected = struct.pack('<Q', 0)
elif mode == 'block_hash_miss':
    h0 = encode_header(EMPTY_OMMERS_HASH, 0, b'\\x00'*8)
    witness_headers = build_ssz_section([h0])
    block_hash = b'\\xee'*32
    expected = struct.pack('<Q', 1)
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

  "$ZISKEMU" -e gen-out/zisk_post_merge_invariants_at_block_hash.elf \
    -i "$in_file" -o "$out_file" -n 6000000 \
    >"$REPO_ROOT/gen-out/zisk_pmibh_${name}.emu.log" 2>&1 || true

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
run_case "canonical_post_merge"               canonical_post_merge || FAILED=1
run_case "ommers_hash_mismatch_status_2"      ommers_hash_mismatch || FAILED=1
run_case "difficulty_nonzero_status_3"        difficulty_nonzero || FAILED=1
run_case "difficulty_large_pow_status_3"      difficulty_large_pow || FAILED=1
run_case "nonce_nonzero_status_4"             nonce_nonzero || FAILED=1
run_case "rlp_field_14_missing_status_5"      rlp_field_14_missing || FAILED=1
run_case "two_headers_pick_second_canonical"  two_headers_pick_second_canonical || FAILED=1
run_case "block_hash_miss_status_1"           block_hash_miss || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: post_merge_invariants_at_block_hash end-to-end"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
