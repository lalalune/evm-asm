#!/usr/bin/env bash
# codegen-zisk-extra-data-at-block-number-check.sh
#
# Number-keyed header.extra_data extractor.
#
# Output (48 bytes):
#   bytes  0.. 8 : status (0..4)
#   bytes  8..16 : extra_data length (u64; 0 on failure)
#   bytes 16..48 : extra_data bytes (zero-padded to 32 B)
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

echo "==> emit zisk_extra_data_at_block_number ELF"
lake exe codegen --program zisk_extra_data_at_block_number \
  --halt linux93 \
  -o gen-out/zisk_extra_data_at_block_number

REPO_ROOT="$(pwd)"

run_case() {
  local name="$1"; shift
  local mode="$1"; shift
  local target="$1"; shift

  local in_file="$REPO_ROOT/gen-out/zisk_edbn_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_edbn_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_edbn_${name}.expected"

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

def encode_header(number_val, extra_data):
    fields = [
        b'\\x11'*32, b'\\x22'*32, b'\\x33'*20, b'\\x44'*32, b'\\x55'*32,
        b'\\x66'*32, b'\\x00'*256, b'',
        shortest_be(number_val), b'\\x83\\xff\\xff\\xff',
        b'', b'\\x83\\x01\\x02\\x03',
        extra_data,                               # 12 extra_data
        b'\\x77'*32, b'\\x00'*8,
    ]
    return rlp.encode(fields)

mode = '$mode'
target = int('$target')
ed_hex = '$ed_hex'

def pad32(b):
    return b + b'\\x00' * (32 - len(b))

if mode == 'extra_data':
    ed = bytes.fromhex(ed_hex)
    h0 = encode_header(target, ed)
    witness_headers = build_ssz_section([h0])
    expected = struct.pack('<Q', 0) + struct.pack('<Q', len(ed)) + pad32(ed)
elif mode == 'pick_second_of_two':
    decoy = b'\\xee' * 4
    real = bytes.fromhex(ed_hex)
    h0 = encode_header(100, decoy)
    h1 = encode_header(target, real)
    witness_headers = build_ssz_section([h0, h1])
    expected = struct.pack('<Q', 0) + struct.pack('<Q', len(real)) + pad32(real)
elif mode == 'number_miss':
    h0 = encode_header(100, b'\\xab')
    witness_headers = build_ssz_section([h0])
    expected = struct.pack('<Q', 1) + struct.pack('<Q', 0) + b'\\x00' * 32
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

  "$ZISKEMU" -e gen-out/zisk_extra_data_at_block_number.elf \
    -i "$in_file" -o "$out_file" -n 4000000 \
    >"$REPO_ROOT/gen-out/zisk_edbn_${name}.emu.log" 2>&1 || true

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
# Geth client-signature pattern (10-byte prefix).
ed_hex="d883010d05846765746888676f312e32312e34"
run_case "geth_client_signature_10b"  extra_data 101 || FAILED=1
ed_hex=""
run_case "empty_extra_data"           extra_data 101 || FAILED=1
ed_hex="$(printf '42%.0s' $(seq 1 32))"
run_case "max_32b_padding"            extra_data 101 || FAILED=1
ed_hex="deadbeef"
run_case "pick_second_of_two"         pick_second_of_two 101 || FAILED=1
ed_hex=""
run_case "number_not_in_section"      number_miss 999 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: extra_data_at_block_number end-to-end"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
