#!/usr/bin/env bash
# codegen-zisk-ommers-hash-at-block-number-check.sh
#
# Number-keyed header.ommers_hash extractor.
#
# Output (40 bytes):
#   bytes  0.. 8 : status (0..3)
#   bytes  8..40 : ommers_hash (32 B; 0 on failure)
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

echo "==> emit zisk_ommers_hash_at_block_number ELF"
lake exe codegen --program zisk_ommers_hash_at_block_number \
  --halt linux93 \
  -o gen-out/zisk_ommers_hash_at_block_number

REPO_ROOT="$(pwd)"

run_case() {
  local name="$1"; shift
  local mode="$1"; shift
  local target="$1"; shift

  local in_file="$REPO_ROOT/gen-out/zisk_ohbn_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_ohbn_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_ohbn_${name}.expected"

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

def shortest_be(n):
    if n == 0: return b''
    nbytes = (n.bit_length() + 7) // 8
    return n.to_bytes(nbytes, 'big')

def encode_header(number_val, ommers_hash):
    fields = [
        b'\\x11'*32, ommers_hash,
        b'\\x33'*20, b'\\x44'*32, b'\\x55'*32,
        b'\\x66'*32, b'\\x00'*256, b'',
        shortest_be(number_val), b'\\x83\\xff\\xff\\xff',
        b'', b'\\x83\\x01\\x02\\x03',
        b'', b'\\x77'*32, b'\\x00'*8,
    ]
    return rlp.encode(fields)

# Post-merge canonical: keccak256(rlp([]))
EMPTY_LIST_KECCAK = k256(rlp.encode([]))

mode = '$mode'
target = int('$target')

if mode == 'post_merge_empty_list':
    ommers = EMPTY_LIST_KECCAK
    h0 = encode_header(target, ommers)
    witness_headers = build_ssz_section([h0])
    expected = struct.pack('<Q', 0) + ommers
elif mode == 'pre_merge_real_ommers':
    ommers = b'\\x42' * 32
    h0 = encode_header(target, ommers)
    witness_headers = build_ssz_section([h0])
    expected = struct.pack('<Q', 0) + ommers
elif mode == 'pick_second_of_two':
    decoy = b'\\x11' * 32
    real = bytes(range(32))
    h0 = encode_header(100, decoy)
    h1 = encode_header(target, real)
    witness_headers = build_ssz_section([h0, h1])
    expected = struct.pack('<Q', 0) + real
elif mode == 'number_miss':
    ommers = EMPTY_LIST_KECCAK
    h0 = encode_header(100, ommers)
    witness_headers = build_ssz_section([h0])
    expected = struct.pack('<Q', 1) + b'\\x00' * 32
else:
    raise SystemExit('bad mode')

with open(sys.argv[1], 'wb') as f:
    record = (
        struct.pack('<Q', len(witness_headers))
        + struct.pack('<Q', target)
        + witness_headers
    )
    f.write(record)
    pad = (-len(record)) % 8
    if pad: f.write(b'\\x00' * pad)

with open(sys.argv[2], 'wb') as f:
    f.write(expected)
" "$in_file" "$exp_file"

  "$ZISKEMU" -e gen-out/zisk_ommers_hash_at_block_number.elf \
    -i "$in_file" -o "$out_file" -n 4000000 \
    >"$REPO_ROOT/gen-out/zisk_ohbn_${name}.emu.log" 2>&1 || true

  local exp_size; exp_size="$(stat -c%s "$exp_file")"
  local actual expected
  actual="$(xxd -p -l "$exp_size" "$out_file" 2>/dev/null | tr -d '\n')"
  expected="$(xxd -p -l "$exp_size" "$exp_file" 2>/dev/null | tr -d '\n')"

  if [[ "$actual" == "$expected" ]]; then
    printf "  %-36s OK   %d bytes match\n" "$name" "$exp_size"
    return 0
  else
    printf "  %-36s FAIL\n    expected: %s\n    actual:   %s\n" \
      "$name" "$expected" "$actual"
    return 1
  fi
}

FAILED=0
run_case "post_merge_canonical_empty"  post_merge_empty_list 101 || FAILED=1
run_case "pre_merge_real_ommers"       pre_merge_real_ommers 101 || FAILED=1
run_case "pick_second_of_two"          pick_second_of_two 101 || FAILED=1
run_case "number_not_in_section"       number_miss 999 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: ommers_hash_at_block_number end-to-end"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
