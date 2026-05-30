#!/usr/bin/env bash
# codegen-zisk-block-hash-at-block-number-check.sh
#
# Number-keyed block_hash lookup. Inverse of #7370.
#
# Output (40 bytes):
#   bytes  0.. 8 : status (0..2)
#   bytes  8..40 : block_hash (32 B; zero on miss)
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

echo "==> emit zisk_block_hash_at_block_number ELF"
lake exe codegen --program zisk_block_hash_at_block_number \
  --halt linux93 \
  -o gen-out/zisk_block_hash_at_block_number

REPO_ROOT="$(pwd)"

run_case() {
  local name="$1"; shift
  local mode="$1"; shift
  local target="$1"; shift

  local in_file="$REPO_ROOT/gen-out/zisk_bhbn_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_bhbn_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_bhbn_${name}.expected"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys
import rlp
from Crypto.Hash import keccak

def k256(b):
    h = keccak.new(digest_bits=256); h.update(b); return h.digest()

def encode_header(number_val):
    if number_val == 0:
        number_field = b''
    else:
        nbytes = (number_val.bit_length() + 7) // 8
        number_field = number_val.to_bytes(nbytes, 'big')
    fields = [
        b'\\x11'*32, b'\\x22'*32, b'\\x33'*20, b'\\x44'*32, b'\\x55'*32,
        b'\\x66'*32, b'\\x00'*256, b'', number_field, b'\\x83\\xff\\xff\\xff',
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
target = int('$target')

if mode == 'three_chain_lookup_first':
    hs = [encode_header(100), encode_header(101), encode_header(102)]
    witness_headers = build_ssz_section(hs)
    expected = struct.pack('<Q', 0) + k256(hs[0])
elif mode == 'three_chain_lookup_middle':
    hs = [encode_header(100), encode_header(101), encode_header(102)]
    witness_headers = build_ssz_section(hs)
    expected = struct.pack('<Q', 0) + k256(hs[1])
elif mode == 'three_chain_lookup_last':
    hs = [encode_header(100), encode_header(101), encode_header(102)]
    witness_headers = build_ssz_section(hs)
    expected = struct.pack('<Q', 0) + k256(hs[2])
elif mode == 'genesis_zero':
    hs = [encode_header(0), encode_header(1)]
    witness_headers = build_ssz_section(hs)
    expected = struct.pack('<Q', 0) + k256(hs[0])
elif mode == 'number_not_in_section':
    hs = [encode_header(100), encode_header(101)]
    witness_headers = build_ssz_section(hs)
    expected = struct.pack('<Q', 1) + b'\\x00' * 32
elif mode == 'empty_section':
    witness_headers = b''
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

  "$ZISKEMU" -e gen-out/zisk_block_hash_at_block_number.elf \
    -i "$in_file" -o "$out_file" -n 4000000 \
    >"$REPO_ROOT/gen-out/zisk_bhbn_${name}.emu.log" 2>&1 || true

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
run_case "three_lookup_first"      three_chain_lookup_first 100 || FAILED=1
run_case "three_lookup_middle"     three_chain_lookup_middle 101 || FAILED=1
run_case "three_lookup_last"       three_chain_lookup_last 102 || FAILED=1
run_case "genesis_zero"            genesis_zero 0 || FAILED=1
run_case "number_not_in_section"   number_not_in_section 999 || FAILED=1
run_case "empty_section"           empty_section 100 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: block_hash_at_block_number end-to-end"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
