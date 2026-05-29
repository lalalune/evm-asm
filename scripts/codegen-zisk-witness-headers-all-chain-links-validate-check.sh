#!/usr/bin/env bash
# codegen-zisk-witness-headers-all-chain-links-validate-check.sh
#
# Batched full-chain validation over witness.headers.
# Returns (valid_count, invalid_count) summing to max(N-1, 0).
#
# Output (24 bytes):
#   bytes  0.. 8 : status (always 0)
#   bytes  8..16 : valid_count
#   bytes 16..24 : invalid_count
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

echo "==> emit zisk_witness_headers_all_chain_links_validate ELF"
lake exe codegen --program zisk_witness_headers_all_chain_links_validate \
  --halt linux93 \
  -o gen-out/zisk_witness_headers_all_chain_links_validate

REPO_ROOT="$(pwd)"

run_case() {
  local name="$1"; shift
  local mode="$1"; shift

  local in_file="$REPO_ROOT/gen-out/zisk_whal_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_whal_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_whal_${name}.expected"

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

def chain_header_seq(n):
    h0 = encode_header(b'\\xab' * 32)
    hs = [h0]
    for _ in range(n - 1):
        hs.append(encode_header(k256(hs[-1])))
    return hs

if mode == 'empty':
    witness_headers = b''
    expected_counts = (0, 0)
elif mode == 'single_header':
    witness_headers = build_ssz_section(chain_header_seq(1))
    expected_counts = (0, 0)
elif mode == 'two_valid':
    witness_headers = build_ssz_section(chain_header_seq(2))
    expected_counts = (1, 0)
elif mode == 'three_valid':
    witness_headers = build_ssz_section(chain_header_seq(3))
    expected_counts = (2, 0)
elif mode == 'three_broken_at_idx0':
    # h1.parent_hash != keccak(h0), h2.parent_hash = keccak(h1).
    h0 = encode_header(b'\\xab' * 32)
    h1 = encode_header(b'\\xee' * 32)
    h2 = encode_header(k256(h1))
    witness_headers = build_ssz_section([h0, h1, h2])
    expected_counts = (1, 1)
elif mode == 'three_all_broken':
    h0 = encode_header(b'\\xab' * 32)
    h1 = encode_header(b'\\xcc' * 32)
    h2 = encode_header(b'\\xdd' * 32)
    witness_headers = build_ssz_section([h0, h1, h2])
    expected_counts = (0, 2)
elif mode == 'three_with_garbage_middle':
    h0 = encode_header(b'\\xab' * 32)
    # middle entry can't be RLP-decoded -> first link (0->1) invalid via
    # K202 fail; second link (1->2) also invalid since header 1 itself
    # can't be the input to header_extract_parent_hash for link 1->2.
    h2 = encode_header(b'\\x99' * 32)
    witness_headers = build_ssz_section([h0, b'\\x00', h2])
    expected_counts = (0, 2)
else:
    raise SystemExit('bad mode')

expected = (
    struct.pack('<Q', 0)
    + struct.pack('<Q', expected_counts[0])
    + struct.pack('<Q', expected_counts[1])
)

with open(sys.argv[1], 'wb') as f:
    record = struct.pack('<Q', len(witness_headers)) + witness_headers
    f.write(record)
    pad = (-len(record)) % 8
    if pad: f.write(b'\\x00' * pad)

with open(sys.argv[2], 'wb') as f:
    f.write(expected)
" "$in_file" "$exp_file"

  "$ZISKEMU" -e gen-out/zisk_witness_headers_all_chain_links_validate.elf \
    -i "$in_file" -o "$out_file" -n 5000000 \
    >"$REPO_ROOT/gen-out/zisk_whal_${name}.emu.log" 2>&1 || true

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
run_case "empty_section"                empty || FAILED=1
run_case "single_header_no_links"       single_header || FAILED=1
run_case "two_valid_link"               two_valid || FAILED=1
run_case "three_valid_chain"            three_valid || FAILED=1
run_case "three_broken_at_idx0"         three_broken_at_idx0 || FAILED=1
run_case "three_all_broken"             three_all_broken || FAILED=1
run_case "three_with_garbage_middle"    three_with_garbage_middle || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: witness_headers_all_chain_links_validate end-to-end"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
