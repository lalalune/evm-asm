#!/usr/bin/env bash
# codegen-zisk-bloom-add-value-check.sh -- PR-K148.
#
# Add a single value (log address or topic) to a 256-byte Ethereum
# log bloom filter, per yellow paper / EIP-2718.
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

echo "==> emit zisk_bloom_add_value ELF"
lake exe codegen --program zisk_bloom_add_value --halt linux93 \
  -o gen-out/zisk_bloom_add_value

REPO_ROOT="$(pwd)"

# run_case <name> <value_hex>
# ziskemu output cap = 256 bytes, the bloom is exactly that size.
# The first run is `add_value(zero_bloom, value)`, so we only check
# the result of adding one value at a time against the Python ref.
run_case() {
  local name="$1" value_hex="$2"

  local in_file="$REPO_ROOT/gen-out/zisk_bloom_add_value_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_bloom_add_value_${name}.output"
  local exp_hex_file="$REPO_ROOT/gen-out/zisk_bloom_add_value_${name}.expected.hex"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys, rlp
try:
    from Crypto.Hash import keccak
    def keccak256(b):
        h = keccak.new(digest_bits=256); h.update(b); return h.digest()
except Exception:
    import sha3
    def keccak256(b): return sha3.keccak_256(b).digest()

value = bytes.fromhex('$value_hex')
bloom = bytearray(256)
h = keccak256(value)
for idx in (0, 2, 4):
    raw_bit = int.from_bytes(h[idx:idx+2], 'big') & 0x07FF
    bit_index = 0x07FF - raw_bit
    byte_index = bit_index // 8
    bit_value = 1 << (7 - (bit_index % 8))
    bloom[byte_index] |= bit_value

with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(value)))
    f.write(value)
    pad = (-(8 + len(value))) % 8
    if pad: f.write(b'\x00' * pad)
with open(sys.argv[2], 'w') as f:
    f.write(bytes(bloom).hex())
" "$in_file" "$exp_hex_file"

  "$ZISKEMU" -e gen-out/zisk_bloom_add_value.elf \
    -i "$in_file" -o "$out_file" -n 5000000 \
    >"$REPO_ROOT/gen-out/zisk_bloom_add_value_${name}.emu.log" 2>&1 || true

  # ziskemu writes the entire 256-byte bloom buffer.
  local actual; actual="$(xxd -p -c 256 "$out_file" | tr -d '\n')"
  local expected; expected="$(cat "$exp_hex_file")"

  if [[ "$actual" == "$expected" ]]; then
    # Count bits set as a sanity check.
    local nbits; nbits="$(python3 -c "print(bin(int('$actual', 16)).count('1'))")"
    printf "  %-30s OK   value=%s... bits_set=%d\n" "$name" "${value_hex:0:16}" "$nbits"
    return 0
  else
    printf "  %-30s FAIL\n" "$name"
    printf "      actual:   %s...\n" "${actual:0:80}"
    printf "      expected: %s...\n" "${expected:0:80}"
    return 1
  fi
}

FAILED=0
# 20-byte address typical
run_case "address_aa"     "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa" || FAILED=1
run_case "address_bb"     "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" || FAILED=1
run_case "address_zero"   "0000000000000000000000000000000000000000" || FAILED=1
# 32-byte topic typical
run_case "topic_32B"      "1111111111111111111111111111111111111111111111111111111111111111" || FAILED=1
# Empty data (degenerate, keccak256(b'') is well-known)
run_case "empty_value"    "" || FAILED=1
# Long-ish bytestring (e.g. some hashed log data)
run_case "longer_input"   "$(python3 -c "print('cafebabe' * 16)")" || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: bloom_add_value matches yellow-paper bloom encoding"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
