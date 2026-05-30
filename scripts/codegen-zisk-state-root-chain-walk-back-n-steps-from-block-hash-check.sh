#!/usr/bin/env bash
# codegen-zisk-state-root-chain-walk-back-n-steps-from-block-hash-check.sh
#
# Multi-step chain walk + state_root extract at the
# deepest reached block.
#
# Output (48 bytes):
#   bytes  0.. 8 : status (0..3)
#   bytes  8..40 : state_root (32 B)
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

echo "==> emit zisk_state_root_chain_walk_back_n_steps_from_block_hash ELF"
lake exe codegen --program zisk_state_root_chain_walk_back_n_steps_from_block_hash \
  --halt linux93 \
  -o gen-out/zisk_state_root_chain_walk_back_n_steps_from_block_hash

REPO_ROOT="$(pwd)"

run_case() {
  local name="$1"; shift
  local mode="$1"; shift
  local n="$1"; shift

  local in_file="$REPO_ROOT/gen-out/zisk_srcw_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_srcw_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_srcw_${name}.expected"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys
import rlp
from Crypto.Hash import keccak

def k256(b):
    h = keccak.new(digest_bits=256); h.update(b); return h.digest()

def encode_header(parent_hash, state_root_byte_fill):
    sr = bytes([state_root_byte_fill]) * 32
    fields = [
        parent_hash, b'\\x22'*32, b'\\x33'*20, sr, b'\\x55'*32,
        b'\\x66'*32, b'\\x00'*256, b'', b'\\x01', b'\\x83\\xff\\xff\\xff',
        b'', b'\\x83\\x01\\x02\\x03', b'', b'\\x77'*32, b'\\x00'*8,
    ]
    return rlp.encode(fields), sr

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

def chain_seq(n_blocks, fills):
    # Build h0 .. h_{n-1} with distinct state_root fills.
    out = []
    parent = b'\\xab' * 32
    for i in range(n_blocks):
        h, sr = encode_header(parent, fills[i])
        out.append((h, sr))
        parent = k256(h)
    return out

if mode == 'walk_3_get_root_at_h0':
    # 4-block chain h0..h3 distinct state_roots; walk 3 back from h3.
    seq = chain_seq(4, [0x44, 0x55, 0x66, 0x77])
    witness_headers = build_ssz_section([h for h, _ in seq])
    start = k256(seq[-1][0])  # h3
    expected_sr = seq[0][1]   # h0.state_root
    expected = (
        struct.pack('<Q', 0)
        + expected_sr
        + struct.pack('<Q', 3)
    )
elif mode == 'walk_zero_return_start_root':
    seq = chain_seq(2, [0x44, 0x55])
    witness_headers = build_ssz_section([h for h, _ in seq])
    start = k256(seq[-1][0])  # h1
    expected_sr = seq[-1][1]
    expected = (
        struct.pack('<Q', 0)
        + expected_sr
        + struct.pack('<Q', 0)
    )
elif mode == 'walk_more_than_available':
    # 3-block chain, request 10 hops -> stops at h0 (boundary), N hops = 2.
    seq = chain_seq(3, [0x44, 0x55, 0x66])
    witness_headers = build_ssz_section([h for h, _ in seq])
    start = k256(seq[-1][0])  # h2
    expected_sr = seq[0][1]   # h0.state_root
    expected = (
        struct.pack('<Q', 0)
        + expected_sr
        + struct.pack('<Q', 2)
    )
elif mode == 'start_missing':
    seq = chain_seq(2, [0x44, 0x55])
    witness_headers = build_ssz_section([h for h, _ in seq])
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

  "$ZISKEMU" -e gen-out/zisk_state_root_chain_walk_back_n_steps_from_block_hash.elf \
    -i "$in_file" -o "$out_file" -n 6000000 \
    >"$REPO_ROOT/gen-out/zisk_srcw_${name}.emu.log" 2>&1 || true

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
run_case "walk_3_get_state_root_at_h0"     walk_3_get_root_at_h0 3 || FAILED=1
run_case "walk_zero_return_start_root"     walk_zero_return_start_root 0 || FAILED=1
run_case "walk_more_than_available"        walk_more_than_available 10 || FAILED=1
run_case "start_block_hash_missing"        start_missing 3 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: state_root_chain_walk_back_n_steps_from_block_hash end-to-end"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
