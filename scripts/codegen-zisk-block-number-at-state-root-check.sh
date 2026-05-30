#!/usr/bin/env bash
# codegen-zisk-block-number-at-state-root-check.sh
#
# Reverse lookup: state_root -> block.number.
#
# Output (16 bytes):
#   bytes  0.. 8 : status (0..3)
#   bytes  8..16 : block_number (u64)
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

echo "==> emit zisk_block_number_at_state_root ELF"
lake exe codegen --program zisk_block_number_at_state_root \
  --halt linux93 \
  -o gen-out/zisk_block_number_at_state_root

REPO_ROOT="$(pwd)"

run_case() {
  local name="$1"; shift
  local mode="$1"; shift

  local in_file="$REPO_ROOT/gen-out/zisk_bnsr_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_bnsr_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_bnsr_${name}.expected"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys
import rlp

def encode_header(number_val, state_root_byte_fill):
    if number_val == 0:
        number_field = b''
    else:
        nbytes = (number_val.bit_length() + 7) // 8
        number_field = number_val.to_bytes(nbytes, 'big')
    sr = bytes([state_root_byte_fill]) * 32
    fields = [
        b'\\x11'*32, b'\\x22'*32, b'\\x33'*20, sr, b'\\x55'*32,
        b'\\x66'*32, b'\\x00'*256, b'', number_field, b'\\x83\\xff\\xff\\xff',
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

if mode == 'three_chain_first':
    seq = [encode_header(100, 0x44), encode_header(101, 0x55), encode_header(102, 0x66)]
    witness_headers = build_ssz_section([h for h, _ in seq])
    target_sr = seq[0][1]
    expected = struct.pack('<Q', 0) + struct.pack('<Q', 100)
elif mode == 'three_chain_middle':
    seq = [encode_header(100, 0x44), encode_header(101, 0x55), encode_header(102, 0x66)]
    witness_headers = build_ssz_section([h for h, _ in seq])
    target_sr = seq[1][1]
    expected = struct.pack('<Q', 0) + struct.pack('<Q', 101)
elif mode == 'three_chain_last':
    seq = [encode_header(100, 0x44), encode_header(101, 0x55), encode_header(102, 0x66)]
    witness_headers = build_ssz_section([h for h, _ in seq])
    target_sr = seq[2][1]
    expected = struct.pack('<Q', 0) + struct.pack('<Q', 102)
elif mode == 'state_root_miss':
    seq = [encode_header(100, 0x44)]
    witness_headers = build_ssz_section([h for h, _ in seq])
    target_sr = b'\\xee' * 32
    expected = struct.pack('<Q', 1) + struct.pack('<Q', 0)
elif mode == 'empty_section':
    witness_headers = b''
    target_sr = b'\\xee' * 32
    expected = struct.pack('<Q', 1) + struct.pack('<Q', 0)
else:
    raise SystemExit('bad mode')

with open(sys.argv[1], 'wb') as f:
    record = (
        struct.pack('<Q', len(witness_headers))
        + target_sr
        + witness_headers
    )
    f.write(record)
    pad = (-len(record)) % 8
    if pad: f.write(b'\\x00' * pad)

with open(sys.argv[2], 'wb') as f:
    f.write(expected)
" "$in_file" "$exp_file"

  "$ZISKEMU" -e gen-out/zisk_block_number_at_state_root.elf \
    -i "$in_file" -o "$out_file" -n 4000000 \
    >"$REPO_ROOT/gen-out/zisk_bnsr_${name}.emu.log" 2>&1 || true

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
run_case "three_chain_first"        three_chain_first || FAILED=1
run_case "three_chain_middle"       three_chain_middle || FAILED=1
run_case "three_chain_last"         three_chain_last || FAILED=1
run_case "state_root_miss"          state_root_miss || FAILED=1
run_case "empty_section"            empty_section || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: block_number_at_state_root end-to-end"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
