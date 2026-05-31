#!/usr/bin/env bash
# codegen-zisk-difficulty-at-block-hash-check.sh
#
# Hash-keyed historical header.difficulty extractor (RLP
# field 7, u64). Mirror of the number-keyed
# `difficulty_at_block_number` but takes a 32-byte
# block_hash key.
#
# Spec-defining check: per EIP-3675 (the Merge), every
# post-merge canonical header MUST have difficulty == 0.
# A non-zero difficulty at the block_hash flags either a
# pre-merge ancestor or a malformed witness.
#
# Output (16 bytes):
#   bytes  0.. 8 : status (0 ok, 1 hash miss, 2 RLP fail / overflow)
#   bytes  8..16 : difficulty u64 LE (0 on failure)
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

echo "==> emit zisk_difficulty_at_block_hash ELF"
lake exe codegen --program zisk_difficulty_at_block_hash \
  --halt linux93 \
  -o gen-out/zisk_difficulty_at_block_hash

REPO_ROOT="$(pwd)"

run_case() {
  local name="$1"; shift
  local mode="$1"; shift

  local in_file="$REPO_ROOT/gen-out/zisk_dfbh_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_dfbh_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_dfbh_${name}.expected"

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

def encode_header(state_root, difficulty_val):
    fields = [
        b'\\x11'*32, b'\\x22'*32, b'\\x33'*20, state_root, b'\\x44'*32,
        b'\\x55'*32, b'\\x00'*256, be_min(difficulty_val), b'\\x01',
        b'\\x83\\xff\\xff\\xff',
        b'', b'\\x83\\x01\\x02\\x03', b'', b'\\x77'*32, b'\\x00'*8,
        b'', b'\\x66'*32, b'', b'', b'\\x99'*32,
    ]
    return rlp.encode(fields)

def encode_header_raw_diff(state_root, diff_bytes):
    fields = [
        b'\\x11'*32, b'\\x22'*32, b'\\x33'*20, state_root, b'\\x44'*32,
        b'\\x55'*32, b'\\x00'*256, diff_bytes, b'\\x01',
        b'\\x83\\xff\\xff\\xff',
        b'', b'\\x83\\x01\\x02\\x03', b'', b'\\x77'*32, b'\\x00'*8,
        b'', b'\\x66'*32, b'', b'', b'\\x99'*32,
    ]
    return rlp.encode(fields)

mode = '$mode'

if mode == 'post_merge_zero':
    h0 = encode_header(b'\\xaa'*32, 0)
    witness_headers = build_ssz_section([h0])
    block_hash = k256(h0)
    expected = struct.pack('<Q', 0) + struct.pack('<Q', 0)
elif mode == 'pre_merge_small_difficulty':
    diff = 0x1A2B3C4D5E6F
    h0 = encode_header(b'\\xaa'*32, diff)
    witness_headers = build_ssz_section([h0])
    block_hash = k256(h0)
    expected = struct.pack('<Q', 0) + struct.pack('<Q', diff)
elif mode == 'pre_merge_u64_max':
    diff = (1 << 64) - 1
    h0 = encode_header(b'\\xaa'*32, diff)
    witness_headers = build_ssz_section([h0])
    block_hash = k256(h0)
    expected = struct.pack('<Q', 0) + struct.pack('<Q', diff)
elif mode == 'pre_merge_u256_overflow':
    # 9-byte difficulty exceeds u64; helper must return status=2.
    h0 = encode_header_raw_diff(b'\\xaa'*32, b'\\x01' + b'\\x00'*8)
    witness_headers = build_ssz_section([h0])
    block_hash = k256(h0)
    expected = struct.pack('<Q', 2) + struct.pack('<Q', 0)
elif mode == 'two_headers_pick_second':
    h0 = encode_header(b'\\xaa'*32, 0xDEAD)
    h1 = encode_header(b'\\xbb'*32, 0)
    witness_headers = build_ssz_section([h0, h1])
    block_hash = k256(h1)
    expected = struct.pack('<Q', 0) + struct.pack('<Q', 0)
elif mode == 'block_hash_miss':
    h0 = encode_header(b'\\xaa'*32, 0)
    witness_headers = build_ssz_section([h0])
    block_hash = b'\\xee'*32
    expected = struct.pack('<Q', 1) + struct.pack('<Q', 0)
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

  "$ZISKEMU" -e gen-out/zisk_difficulty_at_block_hash.elf \
    -i "$in_file" -o "$out_file" -n 6000000 \
    >"$REPO_ROOT/gen-out/zisk_dfbh_${name}.emu.log" 2>&1 || true

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
run_case "post_merge_zero"                  post_merge_zero || FAILED=1
run_case "pre_merge_small_difficulty"       pre_merge_small_difficulty || FAILED=1
run_case "pre_merge_u64_max"                pre_merge_u64_max || FAILED=1
run_case "pre_merge_u256_overflow_status_2" pre_merge_u256_overflow || FAILED=1
run_case "two_headers_pick_second"          two_headers_pick_second || FAILED=1
run_case "block_hash_miss_status_1"         block_hash_miss || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: difficulty_at_block_hash end-to-end"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
