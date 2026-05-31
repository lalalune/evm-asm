#!/usr/bin/env bash
# codegen-zisk-gas-pair-at-block-hash-check.sh
#
# Hash-keyed (gas_used, gas_limit) PAIR extractor (RLP
# fields 10 & 9; both u64). Composite that halves the
# keccak cost vs. calling the two singletons.
#
# Output (24 bytes):
#   bytes  0.. 8 : status (0..3)
#   bytes  8..16 : gas_used  u64 LE (0 on failure)
#   bytes 16..24 : gas_limit u64 LE (0 on failure)
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

echo "==> emit zisk_gas_pair_at_block_hash ELF"
lake exe codegen --program zisk_gas_pair_at_block_hash \
  --halt linux93 \
  -o gen-out/zisk_gas_pair_at_block_hash

REPO_ROOT="$(pwd)"

run_case() {
  local name="$1"; shift
  local mode="$1"; shift

  local in_file="$REPO_ROOT/gen-out/zisk_gpbh_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_gpbh_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_gpbh_${name}.expected"

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

def encode_header(state_root, gas_limit_val, gas_used_val):
    fields = [
        b'\\x11'*32, b'\\x22'*32, b'\\x33'*20, state_root, b'\\x44'*32,
        b'\\x55'*32, b'\\x00'*256, b'', b'\\x01',
        be_min(gas_limit_val),         # field 9
        be_min(gas_used_val),          # field 10
        b'\\x83\\x01\\x02\\x03', b'', b'\\x77'*32, b'\\x00'*8,
        b'', b'\\x66'*32, b'', b'', b'\\x99'*32,
    ]
    return rlp.encode(fields)

def encode_header_raw_fields(state_root, raw9, raw10):
    fields = [
        b'\\x11'*32, b'\\x22'*32, b'\\x33'*20, state_root, b'\\x44'*32,
        b'\\x55'*32, b'\\x00'*256, b'', b'\\x01',
        raw9, raw10,
        b'\\x83\\x01\\x02\\x03', b'', b'\\x77'*32, b'\\x00'*8,
        b'', b'\\x66'*32, b'', b'', b'\\x99'*32,
    ]
    return rlp.encode(fields)

mode = '$mode'

if mode == 'mainnet_typical_block':
    gl = 30_000_000     # mainnet gas limit floor
    gu = 14_500_000     # ~48% utilization
    h0 = encode_header(b'\\xaa'*32, gl, gu)
    witness_headers = build_ssz_section([h0])
    block_hash = k256(h0)
    expected = (struct.pack('<Q', 0)
                + struct.pack('<Q', gu)
                + struct.pack('<Q', gl))
elif mode == 'fully_saturated_block':
    gl = 30_000_000
    gu = 30_000_000     # at-cap; legal but extreme
    h0 = encode_header(b'\\xaa'*32, gl, gu)
    witness_headers = build_ssz_section([h0])
    block_hash = k256(h0)
    expected = (struct.pack('<Q', 0)
                + struct.pack('<Q', gu)
                + struct.pack('<Q', gl))
elif mode == 'empty_block_zero_gas_used':
    gl = 30_000_000
    gu = 0
    h0 = encode_header(b'\\xaa'*32, gl, gu)
    witness_headers = build_ssz_section([h0])
    block_hash = k256(h0)
    expected = (struct.pack('<Q', 0)
                + struct.pack('<Q', 0)
                + struct.pack('<Q', gl))
elif mode == 'two_headers_pick_second':
    h0 = encode_header(b'\\xaa'*32, 30_000_000, 1)
    h1 = encode_header(b'\\xbb'*32, 30_000_000, 21_000)
    witness_headers = build_ssz_section([h0, h1])
    block_hash = k256(h1)
    expected = (struct.pack('<Q', 0)
                + struct.pack('<Q', 21_000)
                + struct.pack('<Q', 30_000_000))
elif mode == 'block_hash_miss':
    h0 = encode_header(b'\\xaa'*32, 30_000_000, 21_000)
    witness_headers = build_ssz_section([h0])
    block_hash = b'\\xee'*32
    expected = struct.pack('<Q', 1) + struct.pack('<Q', 0) + struct.pack('<Q', 0)
elif mode == 'gas_used_overflow_status_2':
    # 9-byte field 10 -> gas_used extractor returns 2 -> our status=2.
    h0 = encode_header_raw_fields(b'\\xaa'*32, be_min(30_000_000),
                                   b'\\x01' + b'\\x00'*8)
    witness_headers = build_ssz_section([h0])
    block_hash = k256(h0)
    expected = struct.pack('<Q', 2) + struct.pack('<Q', 0) + struct.pack('<Q', 0)
elif mode == 'gas_limit_overflow_status_3':
    # 9-byte field 9 -> gas_limit fails AFTER gas_used (=21000) succeeded
    h0 = encode_header_raw_fields(b'\\xaa'*32, b'\\x01' + b'\\x00'*8,
                                   be_min(21_000))
    witness_headers = build_ssz_section([h0])
    block_hash = k256(h0)
    expected = struct.pack('<Q', 3) + struct.pack('<Q', 0) + struct.pack('<Q', 0)
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

  "$ZISKEMU" -e gen-out/zisk_gas_pair_at_block_hash.elf \
    -i "$in_file" -o "$out_file" -n 6000000 \
    >"$REPO_ROOT/gen-out/zisk_gpbh_${name}.emu.log" 2>&1 || true

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
run_case "mainnet_typical_block"              mainnet_typical_block || FAILED=1
run_case "fully_saturated_block"              fully_saturated_block || FAILED=1
run_case "empty_block_zero_gas_used"          empty_block_zero_gas_used || FAILED=1
run_case "two_headers_pick_second"            two_headers_pick_second || FAILED=1
run_case "block_hash_miss_status_1"           block_hash_miss || FAILED=1
run_case "gas_used_overflow_status_2"         gas_used_overflow_status_2 || FAILED=1
run_case "gas_limit_overflow_status_3"        gas_limit_overflow_status_3 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: gas_pair_at_block_hash end-to-end"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
