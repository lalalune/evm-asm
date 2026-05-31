#!/usr/bin/env bash
# codegen-zisk-beneficiary-at-block-hash-check.sh
#
# Hash-keyed header.beneficiary extractor.
#
# Output (28 bytes):
#   bytes  0.. 8 : status (0..2)
#   bytes  8..28 : beneficiary (20 B; 0 on failure)
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

echo "==> emit zisk_beneficiary_at_block_hash ELF"
lake exe codegen --program zisk_beneficiary_at_block_hash \
  --halt linux93 \
  -o gen-out/zisk_beneficiary_at_block_hash

REPO_ROOT="$(pwd)"

run_case() {
  local name="$1"; shift
  local mode="$1"; shift

  local in_file="$REPO_ROOT/gen-out/zisk_bnbh_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_bnbh_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_bnbh_${name}.expected"

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

def encode_header(number_val, beneficiary):
    fields = [
        b'\\x11'*32, b'\\x22'*32, beneficiary,
        b'\\x44'*32, b'\\x55'*32,
        b'\\x66'*32, b'\\x00'*256, b'',
        shortest_be(number_val), b'\\x83\\xff\\xff\\xff',
        b'', b'\\x83\\x01\\x02\\x03',
        b'', b'\\x77'*32, b'\\x00'*8,
    ]
    return rlp.encode(fields)

mode = '$mode'

if mode == 'mev_proposer':
    beneficiary = bytes.fromhex('dafea492d9c6733ae3d56b7ed1adb60692c98bc5')
    h0 = encode_header(101, beneficiary)
    witness_headers = build_ssz_section([h0])
    block_hash = k256(h0)
    expected = struct.pack('<Q', 0) + beneficiary
elif mode == 'zero_address':
    beneficiary = b'\\x00' * 20
    h0 = encode_header(101, beneficiary)
    witness_headers = build_ssz_section([h0])
    block_hash = k256(h0)
    expected = struct.pack('<Q', 0) + beneficiary
elif mode == 'pick_second_of_two':
    decoy = b'\\x11' * 20
    real = bytes(range(20))
    h0 = encode_header(100, decoy)
    h1 = encode_header(101, real)
    witness_headers = build_ssz_section([h0, h1])
    block_hash = k256(h1)
    expected = struct.pack('<Q', 0) + real
elif mode == 'block_hash_miss':
    beneficiary = b'\\xaa' * 20
    h0 = encode_header(101, beneficiary)
    witness_headers = build_ssz_section([h0])
    block_hash = b'\\xee' * 32
    expected = struct.pack('<Q', 1) + b'\\x00' * 20
else:
    raise SystemExit('bad mode')

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

  "$ZISKEMU" -e gen-out/zisk_beneficiary_at_block_hash.elf \
    -i "$in_file" -o "$out_file" -n 4000000 \
    >"$REPO_ROOT/gen-out/zisk_bnbh_${name}.emu.log" 2>&1 || true

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
run_case "mev_proposer_address"      mev_proposer || FAILED=1
run_case "zero_address"              zero_address || FAILED=1
run_case "pick_second_of_two"        pick_second_of_two || FAILED=1
run_case "block_hash_miss"           block_hash_miss || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: beneficiary_at_block_hash end-to-end"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
