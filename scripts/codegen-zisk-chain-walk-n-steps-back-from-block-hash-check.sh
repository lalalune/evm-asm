#!/usr/bin/env bash
# codegen-zisk-chain-walk-n-steps-back-from-block-hash-check.sh
#
# Multi-step backward chain walk. Iterates one-step walks N
# times or until parent isn't in witness.
#
# Output (48 bytes):
#   bytes  0.. 8 : status (0..2)
#   bytes  8..40 : final_block_hash (32 B)
#   bytes 40..48 : valid_steps_count (u64)
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

echo "==> emit zisk_chain_walk_n_steps_back_from_block_hash ELF"
lake exe codegen --program zisk_chain_walk_n_steps_back_from_block_hash \
  --halt linux93 \
  -o gen-out/zisk_chain_walk_n_steps_back_from_block_hash

REPO_ROOT="$(pwd)"

run_case() {
  local name="$1"; shift
  local mode="$1"; shift
  local n="$1"; shift

  local in_file="$REPO_ROOT/gen-out/zisk_cwnsb_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_cwnsb_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_cwnsb_${name}.expected"

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
N = int('$n')

def chain_seq(n_blocks):
    # Construct a sequence of headers h_0 -> h_1 -> ... -> h_{n-1}
    # where each header's parent_hash is keccak(previous).
    out = [encode_header(b'\\xab' * 32)]
    for _ in range(n_blocks - 1):
        out.append(encode_header(k256(out[-1])))
    return out

if mode == 'four_chain_walk_3_from_top':
    # h0 -> h1 -> h2 -> h3, start from h3, walk 3 back -> should reach h0.
    hs = chain_seq(4)
    witness_headers = build_ssz_section(hs)
    start = k256(hs[-1])  # h3
    final_hash = k256(hs[0])  # h0
    expected = (
        struct.pack('<Q', 0)
        + final_hash
        + struct.pack('<Q', 3)
    )
elif mode == 'walk_more_than_available':
    # h0 -> h1 -> h2, start from h2, walk 5 back -> boundary after 2 hops.
    hs = chain_seq(3)
    witness_headers = build_ssz_section(hs)
    start = k256(hs[-1])
    final_hash = k256(hs[0])  # we walk h2 -> h1 -> h0, then h0.parent is not in witness
    expected = (
        struct.pack('<Q', 0)
        + final_hash
        + struct.pack('<Q', 2)
    )
elif mode == 'walk_zero_steps':
    hs = chain_seq(3)
    witness_headers = build_ssz_section(hs)
    start = k256(hs[-1])
    expected = (
        struct.pack('<Q', 0)
        + start  # current never advanced; final = start
        + struct.pack('<Q', 0)
    )
elif mode == 'start_missing':
    hs = chain_seq(2)
    witness_headers = build_ssz_section(hs)
    start = b'\\xee' * 32
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
        + struct.pack('<Q', N)
        + start
        + witness_headers
    )
    f.write(record)
    pad = (-len(record)) % 8
    if pad: f.write(b'\\x00' * pad)

with open(sys.argv[2], 'wb') as f:
    f.write(expected)
" "$in_file" "$exp_file"

  "$ZISKEMU" -e gen-out/zisk_chain_walk_n_steps_back_from_block_hash.elf \
    -i "$in_file" -o "$out_file" -n 6000000 \
    >"$REPO_ROOT/gen-out/zisk_cwnsb_${name}.emu.log" 2>&1 || true

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
# 1) 4-block chain, walk 3 steps from top -> reach h0.
run_case "four_chain_walk_3"           four_chain_walk_3_from_top 3 || FAILED=1
# 2) 3-block chain, request 5 hops -> stop at boundary after 2 valid hops.
run_case "walk_more_than_available"    walk_more_than_available 5 || FAILED=1
# 3) Request 0 hops -> final = start, count = 0.
run_case "walk_zero_steps"             walk_zero_steps 0 || FAILED=1
# 4) Start hash not in witness -> status 1.
run_case "start_block_hash_missing"    start_missing 3 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: chain_walk_n_steps_back_from_block_hash end-to-end"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
