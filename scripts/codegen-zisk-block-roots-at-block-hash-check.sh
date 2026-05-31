#!/usr/bin/env bash
# codegen-zisk-block-roots-at-block-hash-check.sh
#
# Hash-keyed (transactions_root, receipts_root, withdrawals_root)
# triple extractor (RLP fields 4, 5, 16). Composite; halves the
# keccak cost vs. calling the three singletons.
#
# Output (104 bytes):
#   bytes   0.. 8 : status (0..4)
#   bytes   8..40 : transactions_root (32 B)
#   bytes  40..72 : receipts_root     (32 B)
#   bytes  72..104: withdrawals_root  (32 B; Shanghai+)
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

echo "==> emit zisk_block_roots_at_block_hash ELF"
lake exe codegen --program zisk_block_roots_at_block_hash \
  --halt linux93 \
  -o gen-out/zisk_block_roots_at_block_hash

REPO_ROOT="$(pwd)"

run_case() {
  local name="$1"; shift
  local mode="$1"; shift

  local in_file="$REPO_ROOT/gen-out/zisk_brbh_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_brbh_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_brbh_${name}.expected"

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

def encode_header(state_root, txs_root, rcpts_root, withdrawals_root, n_fields=20):
    fields = [
        b'\\x11'*32, b'\\x22'*32, b'\\x33'*20, state_root, txs_root,
        rcpts_root, b'\\x00'*256, b'', b'\\x01', b'\\x83\\xff\\xff\\xff',
        b'', b'\\x83\\x01\\x02\\x03', b'', b'\\x77'*32, b'\\x00'*8,
        b'',                # base_fee_per_gas (15)
        withdrawals_root,   # (16)
        b'', b'', b'\\x99'*32,
    ]
    return rlp.encode(fields[:n_fields])

def encode_header_raw_f4(state_root, raw4_bytes, rcpts_root, withdrawals_root):
    # forces field-4 size mismatch
    fields = [
        b'\\x11'*32, b'\\x22'*32, b'\\x33'*20, state_root, raw4_bytes,
        rcpts_root, b'\\x00'*256, b'', b'\\x01', b'\\x83\\xff\\xff\\xff',
        b'', b'\\x83\\x01\\x02\\x03', b'', b'\\x77'*32, b'\\x00'*8,
        b'', withdrawals_root, b'', b'', b'\\x99'*32,
    ]
    return rlp.encode(fields)

def encode_header_raw_f5(state_root, txs_root, raw5_bytes, withdrawals_root):
    # forces field-5 size mismatch
    fields = [
        b'\\x11'*32, b'\\x22'*32, b'\\x33'*20, state_root, txs_root,
        raw5_bytes, b'\\x00'*256, b'', b'\\x01', b'\\x83\\xff\\xff\\xff',
        b'', b'\\x83\\x01\\x02\\x03', b'', b'\\x77'*32, b'\\x00'*8,
        b'', withdrawals_root, b'', b'', b'\\x99'*32,
    ]
    return rlp.encode(fields)

mode = '$mode'

if mode == 'distinct_triple':
    tx = bytes(range(32))
    rc = bytes(range(32, 64))
    wd = bytes(range(64, 96))
    h0 = encode_header(b'\\xaa'*32, tx, rc, wd)
    witness_headers = build_ssz_section([h0])
    block_hash = k256(h0)
    expected = struct.pack('<Q', 0) + tx + rc + wd
elif mode == 'two_headers_pick_second':
    tx0 = b'\\x00'*32; rc0 = b'\\x00'*32; wd0 = b'\\x00'*32
    tx1 = bytes(range(31, -1, -1))
    rc1 = bytes(range(63, 31, -1))
    wd1 = bytes(range(95, 63, -1))
    h0 = encode_header(b'\\xaa'*32, tx0, rc0, wd0)
    h1 = encode_header(b'\\xbb'*32, tx1, rc1, wd1)
    witness_headers = build_ssz_section([h0, h1])
    block_hash = k256(h1)
    expected = struct.pack('<Q', 0) + tx1 + rc1 + wd1
elif mode == 'block_hash_miss':
    h0 = encode_header(b'\\xaa'*32, b'\\x11'*32, b'\\x22'*32, b'\\x33'*32)
    witness_headers = build_ssz_section([h0])
    block_hash = b'\\xee'*32
    expected = struct.pack('<Q', 1) + b'\\x00'*32 + b'\\x00'*32 + b'\\x00'*32
elif mode == 'txs_root_size_mismatch_status_2':
    h0 = encode_header_raw_f4(b'\\xaa'*32, b'\\x77'*31, b'\\x22'*32, b'\\x33'*32)
    witness_headers = build_ssz_section([h0])
    block_hash = k256(h0)
    expected = struct.pack('<Q', 2) + b'\\x00'*32 + b'\\x00'*32 + b'\\x00'*32
elif mode == 'receipts_root_size_mismatch_status_3':
    h0 = encode_header_raw_f5(b'\\xaa'*32, b'\\x11'*32, b'\\x22'*31, b'\\x33'*32)
    witness_headers = build_ssz_section([h0])
    block_hash = k256(h0)
    expected = struct.pack('<Q', 3) + b'\\x00'*32 + b'\\x00'*32 + b'\\x00'*32
elif mode == 'pre_shanghai_withdrawals_absent_status_4':
    # 16-field header has no field 16 (= withdrawals_root); the
    # third extractor call will fail.
    h0 = encode_header(b'\\xaa'*32, b'\\x11'*32, b'\\x22'*32, b'\\x33'*32, n_fields=16)
    witness_headers = build_ssz_section([h0])
    block_hash = k256(h0)
    expected = struct.pack('<Q', 4) + b'\\x00'*32 + b'\\x00'*32 + b'\\x00'*32
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

  "$ZISKEMU" -e gen-out/zisk_block_roots_at_block_hash.elf \
    -i "$in_file" -o "$out_file" -n 6000000 \
    >"$REPO_ROOT/gen-out/zisk_brbh_${name}.emu.log" 2>&1 || true

  local exp_size
  exp_size="$(stat -c%s "$exp_file")"
  local actual expected
  actual="$(xxd -p -l "$exp_size" "$out_file" 2>/dev/null | tr -d '\n')"
  expected="$(xxd -p -l "$exp_size" "$exp_file" 2>/dev/null | tr -d '\n')"

  if [[ "$actual" == "$expected" ]]; then
    printf "  %-46s OK   %d bytes match\n" "$name" "$exp_size"
    return 0
  else
    printf "  %-46s FAIL\n    expected: %s\n    actual:   %s\n" \
      "$name" "$expected" "$actual"
    return 1
  fi
}

FAILED=0
run_case "distinct_triple"                          distinct_triple || FAILED=1
run_case "two_headers_pick_second"                  two_headers_pick_second || FAILED=1
run_case "block_hash_miss_status_1"                 block_hash_miss || FAILED=1
run_case "txs_root_size_mismatch_status_2"          txs_root_size_mismatch_status_2 || FAILED=1
run_case "receipts_root_size_mismatch_status_3"     receipts_root_size_mismatch_status_3 || FAILED=1
run_case "pre_shanghai_withdrawals_absent_status_4" pre_shanghai_withdrawals_absent_status_4 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: block_roots_at_block_hash end-to-end"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
