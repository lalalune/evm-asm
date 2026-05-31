#!/usr/bin/env bash
# codegen-zisk-number-timestamp-pair-at-block-hash-check.sh
#
# Hash-keyed (block.number, block.timestamp) PAIR extractor
# (RLP fields 8 & 11; both u64). Composite that halves the
# keccak cost vs. calling the two singletons.
#
# Output (24 bytes):
#   bytes  0.. 8 : status (0..3)
#   bytes  8..16 : block.number    u64 LE (0 on failure)
#   bytes 16..24 : block.timestamp u64 LE (0 on failure)
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

echo "==> emit zisk_number_timestamp_pair_at_block_hash ELF"
lake exe codegen --program zisk_number_timestamp_pair_at_block_hash \
  --halt linux93 \
  -o gen-out/zisk_number_timestamp_pair_at_block_hash

REPO_ROOT="$(pwd)"

run_case() {
  local name="$1"; shift
  local mode="$1"; shift

  local in_file="$REPO_ROOT/gen-out/zisk_ntpbh_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_ntpbh_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_ntpbh_${name}.expected"

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

def encode_header(state_root, number_val, timestamp_val):
    fields = [
        b'\\x11'*32, b'\\x22'*32, b'\\x33'*20, state_root, b'\\x44'*32,
        b'\\x55'*32, b'\\x00'*256, b'',
        be_min(number_val),         # field 8
        b'\\x83\\xff\\xff\\xff',
        b'',
        be_min(timestamp_val),      # field 11
        b'', b'\\x77'*32, b'\\x00'*8,
        b'', b'\\x66'*32, b'', b'', b'\\x99'*32,
    ]
    return rlp.encode(fields)

def encode_header_raw_field(state_root, raw_field_8, raw_field_11):
    fields = [
        b'\\x11'*32, b'\\x22'*32, b'\\x33'*20, state_root, b'\\x44'*32,
        b'\\x55'*32, b'\\x00'*256, b'', raw_field_8, b'\\x83\\xff\\xff\\xff',
        b'', raw_field_11, b'', b'\\x77'*32, b'\\x00'*8,
        b'', b'\\x66'*32, b'', b'', b'\\x99'*32,
    ]
    return rlp.encode(fields)

mode = '$mode'

if mode == 'mainnet_recent_pair':
    nu = 19_500_000
    ts = 1_725_000_000  # 2024-09-ish Unix time
    h0 = encode_header(b'\\xaa'*32, nu, ts)
    witness_headers = build_ssz_section([h0])
    block_hash = k256(h0)
    expected = (struct.pack('<Q', 0)
                + struct.pack('<Q', nu)
                + struct.pack('<Q', ts))
elif mode == 'genesis_zero_pair':
    h0 = encode_header(b'\\xaa'*32, 0, 0)
    witness_headers = build_ssz_section([h0])
    block_hash = k256(h0)
    expected = struct.pack('<Q', 0) + struct.pack('<Q', 0) + struct.pack('<Q', 0)
elif mode == 'u64_max_pair':
    val = (1 << 64) - 1
    h0 = encode_header(b'\\xaa'*32, val, val)
    witness_headers = build_ssz_section([h0])
    block_hash = k256(h0)
    expected = (struct.pack('<Q', 0)
                + struct.pack('<Q', val)
                + struct.pack('<Q', val))
elif mode == 'two_headers_pick_second':
    h0 = encode_header(b'\\xaa'*32, 1, 100)
    h1 = encode_header(b'\\xbb'*32, 19_500_001, 1_725_000_012)
    witness_headers = build_ssz_section([h0, h1])
    block_hash = k256(h1)
    expected = (struct.pack('<Q', 0)
                + struct.pack('<Q', 19_500_001)
                + struct.pack('<Q', 1_725_000_012))
elif mode == 'block_hash_miss':
    h0 = encode_header(b'\\xaa'*32, 1, 100)
    witness_headers = build_ssz_section([h0])
    block_hash = b'\\xee'*32
    expected = struct.pack('<Q', 1) + struct.pack('<Q', 0) + struct.pack('<Q', 0)
elif mode == 'number_overflow_status_2':
    # 9-byte field 8 -> number extractor returns 2 -> our status=2.
    h0 = encode_header_raw_field(b'\\xaa'*32,
                                 b'\\x01' + b'\\x00'*8,
                                 be_min(123))
    witness_headers = build_ssz_section([h0])
    block_hash = k256(h0)
    expected = struct.pack('<Q', 2) + struct.pack('<Q', 0) + struct.pack('<Q', 0)
elif mode == 'timestamp_overflow_status_3':
    # 9-byte field 11 -> our status=3.
    h0 = encode_header_raw_field(b'\\xaa'*32,
                                 be_min(123),
                                 b'\\x01' + b'\\x00'*8)
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

  "$ZISKEMU" -e gen-out/zisk_number_timestamp_pair_at_block_hash.elf \
    -i "$in_file" -o "$out_file" -n 6000000 \
    >"$REPO_ROOT/gen-out/zisk_ntpbh_${name}.emu.log" 2>&1 || true

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
run_case "mainnet_recent_pair"                mainnet_recent_pair || FAILED=1
run_case "genesis_zero_pair"                  genesis_zero_pair || FAILED=1
run_case "u64_max_pair"                       u64_max_pair || FAILED=1
run_case "two_headers_pick_second"            two_headers_pick_second || FAILED=1
run_case "block_hash_miss_status_1"           block_hash_miss || FAILED=1
run_case "number_overflow_status_2"           number_overflow_status_2 || FAILED=1
run_case "timestamp_overflow_status_3"        timestamp_overflow_status_3 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: number_timestamp_pair_at_block_hash end-to-end"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
