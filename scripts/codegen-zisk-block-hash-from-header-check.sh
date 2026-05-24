#!/usr/bin/env bash
# codegen-zisk-block-hash-from-header-check.sh -- PR-K172.
#
# Block hash = keccak256(header_rlp_bytes). Verifies the one-shot
# header-hash primitive against the Python keccak256 reference for a
# few representative header shapes.
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

echo "==> emit zisk_block_hash_from_header ELF"
lake exe codegen --program zisk_block_hash_from_header --halt linux93 \
  -o gen-out/zisk_block_hash_from_header

REPO_ROOT="$(pwd)"

# run_case <name> <python expression returning a list of 15+ field bytes>
run_case() {
  local name="$1" field_expr="$2"

  local in_file="$REPO_ROOT/gen-out/zisk_block_hash_from_header_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_block_hash_from_header_${name}.output"
  local exp_hex_file="$REPO_ROOT/gen-out/zisk_block_hash_from_header_${name}.expected.hex"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys, rlp
try:
    from Crypto.Hash import keccak
    def keccak256(b):
        h = keccak.new(digest_bits=256); h.update(b); return h.digest()
except Exception:
    import sha3
    def keccak256(b): return sha3.keccak_256(b).digest()

fields = $field_expr
header_rlp = rlp.encode(fields)
block_hash = keccak256(header_rlp)

with open(sys.argv[1], 'wb') as f:
    record = struct.pack('<Q', len(header_rlp)) + header_rlp
    f.write(record)
    pad = (-len(record)) % 8
    if pad: f.write(b'\x00' * pad)
with open(sys.argv[2], 'w') as f:
    f.write(block_hash.hex())
" "$in_file" "$exp_hex_file"

  "$ZISKEMU" -e gen-out/zisk_block_hash_from_header.elf \
    -i "$in_file" -o "$out_file" -n 1000000 \
    >"$REPO_ROOT/gen-out/zisk_block_hash_from_header_${name}.emu.log" 2>&1 || true

  local actual; actual="$(xxd -p -l 32 "$out_file" | tr -d '\n')"
  local expected; expected="$(cat "$exp_hex_file")"

  if [[ "$actual" == "$expected" ]]; then
    printf "  %-30s OK   hash=%s...\n" "$name" "${actual:0:16}"
    return 0
  else
    printf "  %-30s FAIL\n" "$name"
    printf "      actual:   %s\n" "$actual"
    printf "      expected: %s\n" "$expected"
    return 1
  fi
}

FAILED=0
# Minimal pre-London header: 15 fields, no base_fee.
run_case "pre_london_15_fields" "[
    b'\\x11'*32, b'\\x22'*32, b'\\x33'*20, b'\\x44'*32, b'\\x55'*32,
    b'\\x66'*32, b'\\x00'*256, b'', b'\\x01', b'\\x83\\xff\\xff\\xff',
    b'', b'\\x83\\x01\\x02\\x03', b'', b'\\x77'*32, b'\\x00'*8,
]" || FAILED=1
# London header: 16 fields (+ base_fee).
run_case "london_16_fields" "[
    b'\\xaa'*32, b'\\xbb'*32, b'\\xcc'*20, b'\\xdd'*32, b'\\xee'*32,
    b'\\xff'*32, b'\\x00'*256, b'', b'\\x80\\x00', b'\\x84\\x01\\x02\\x03\\x04',
    b'\\x82\\x02\\x00', b'\\x83\\x05\\x06\\x07', b'\\x88abcdefgh', b'\\x88'*32, b'\\x00'*8,
    b'\\x82\\x12\\x34',
]" || FAILED=1
# Shanghai-style header: 17 fields (+ withdrawals_root).
run_case "shanghai_17_fields" "[
    b'\\x01'*32, b'\\x02'*32, b'\\x03'*20, b'\\x04'*32, b'\\x05'*32,
    b'\\x06'*32, b'\\x00'*256, b'', b'\\x83\\x10\\x00\\x00', b'\\x83\\xff\\xff\\xff',
    b'', b'\\x83\\x01\\x02\\x03', b'', b'\\x07'*32, b'\\x00'*8,
    b'\\x82\\xab\\xcd', b'\\x08'*32,
]" || FAILED=1
# Cancun-style header: 20 fields (+ blob_gas_used, excess_blob_gas, parent_beacon_block_root).
run_case "cancun_20_fields" "[
    b'\\x1a'*32, b'\\x2b'*32, b'\\x3c'*20, b'\\x4d'*32, b'\\x5e'*32,
    b'\\x6f'*32, b'\\x00'*256, b'', b'\\x84\\x12\\x34\\x56\\x78', b'\\x83\\xff\\xff\\xff',
    b'', b'\\x83\\x01\\x02\\x03', b'', b'\\x9a'*32, b'\\x00'*8,
    b'\\x82\\xab\\xcd', b'\\xab'*32, b'\\x82\\x00\\x01', b'\\x82\\x00\\x02', b'\\xbc'*32,
]" || FAILED=1
# Empty extra_data + non-zero number/timestamp shape (smoke-test for short fields).
run_case "small_numbers" "[
    b'\\x00'*32, b'\\x00'*32, b'\\x00'*20, b'\\x00'*32, b'\\x00'*32,
    b'\\x00'*32, b'\\x00'*256, b'\\x01', b'\\x02', b'\\x03',
    b'\\x04', b'\\x05', b'', b'\\x00'*32, b'\\x00'*8,
]" || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: block_hash_from_header matches Python keccak256(header_rlp)"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
