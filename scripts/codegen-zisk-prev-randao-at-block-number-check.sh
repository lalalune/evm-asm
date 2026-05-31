#!/usr/bin/env bash
# codegen-zisk-prev-randao-at-block-number-check.sh
#
# Number-keyed header.prev_randao extractor.
#
# Output (40 bytes):
#   bytes  0.. 8 : status (0..3)
#   bytes  8..40 : prev_randao (32 B; 0 on failure)
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

echo "==> emit zisk_prev_randao_at_block_number ELF"
lake exe codegen --program zisk_prev_randao_at_block_number \
  --halt linux93 \
  -o gen-out/zisk_prev_randao_at_block_number

REPO_ROOT="$(pwd)"

run_case() {
  local name="$1"; shift
  local mode="$1"; shift
  local target="$1"; shift

  local in_file="$REPO_ROOT/gen-out/zisk_prbn_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_prbn_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_prbn_${name}.expected"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys
import rlp

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

def encode_header(number_val, prev_randao):
    # prev_randao is field index 13 (mix_hash slot post-merge).
    fields = [
        b'\\x11'*32, b'\\x22'*32, b'\\x33'*20, b'\\x44'*32, b'\\x55'*32,
        b'\\x66'*32, b'\\x00'*256, b'',
        shortest_be(number_val), b'\\x83\\xff\\xff\\xff',
        b'', b'\\x83\\x01\\x02\\x03',
        b'',                                      # idx 12: extra_data
        prev_randao,                              # idx 13: prev_randao
        b'\\x00'*8,                               # idx 14: nonce
    ]
    return rlp.encode(fields)

mode = '$mode'
target = int('$target')

if mode == 'random_pattern':
    prev_randao = b'\\xde\\xad\\xbe\\xef' * 8
    h0 = encode_header(target, prev_randao)
    witness_headers = build_ssz_section([h0])
    expected = struct.pack('<Q', 0) + prev_randao
elif mode == 'zero_randao':
    prev_randao = b'\\x00' * 32
    h0 = encode_header(target, prev_randao)
    witness_headers = build_ssz_section([h0])
    expected = struct.pack('<Q', 0) + prev_randao
elif mode == 'pick_second_of_two':
    decoy = b'\\x11' * 32
    real = bytes(range(32))
    h0 = encode_header(100, decoy)
    h1 = encode_header(target, real)
    witness_headers = build_ssz_section([h0, h1])
    expected = struct.pack('<Q', 0) + real
elif mode == 'number_miss':
    prev_randao = b'\\xab' * 32
    h0 = encode_header(100, prev_randao)
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

  "$ZISKEMU" -e gen-out/zisk_prev_randao_at_block_number.elf \
    -i "$in_file" -o "$out_file" -n 4000000 \
    >"$REPO_ROOT/gen-out/zisk_prbn_${name}.emu.log" 2>&1 || true

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
run_case "random_deadbeef_pattern"   random_pattern 101 || FAILED=1
run_case "zero_randao_edge_case"     zero_randao 101 || FAILED=1
run_case "pick_second_of_two"        pick_second_of_two 101 || FAILED=1
run_case "number_not_in_section"     number_miss 999 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: prev_randao_at_block_number end-to-end"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
