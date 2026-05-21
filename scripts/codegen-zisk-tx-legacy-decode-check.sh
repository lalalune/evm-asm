#!/usr/bin/env bash
# codegen-zisk-tx-legacy-decode-check.sh -- PR-K36.
#
# Decode all 9 fields of a legacy Ethereum tx into a 196-byte
# struct. Cross-validated against Python's RLP encoder.
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

echo "==> emit zisk_tx_legacy_decode ELF"
lake exe codegen --program zisk_tx_legacy_decode --halt linux93 \
  -o gen-out/zisk_tx_legacy_decode

REPO_ROOT="$(pwd)"

run_case() {
  local name="$1" nonce="$2" gas_price="$3" gas_limit="$4" to_hex="$5" value="$6" data_hex="$7" v="$8" r_hex="$9" s_hex="${10}"

  local in_file="$REPO_ROOT/gen-out/zisk_tx_legacy_decode_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_tx_legacy_decode_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_tx_legacy_decode_${name}.expected"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys
import rlp

nonce = $nonce
gas_price = $gas_price
gas_limit = $gas_limit
to = bytes.fromhex('$to_hex')
value = $value
data = bytes.fromhex('$data_hex')
v = $v
r = int.from_bytes(bytes.fromhex('$r_hex'), 'big')
s = int.from_bytes(bytes.fromhex('$s_hex'), 'big')

tx_rlp = rlp.encode([nonce, gas_price, gas_limit, to, value, data, v, r, s])
with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(tx_rlp)))
    f.write(tx_rlp)
    pad = (-(8 + len(tx_rlp))) % 8
    if pad:
        f.write(b'\x00' * pad)

# Expected output: status (u64 LE) + 196-byte struct
expected = struct.pack('<Q', 0)
expected += struct.pack('<Q', nonce)
expected += gas_price.to_bytes(32, 'big')
expected += struct.pack('<Q', gas_limit)
to_present = 1 if len(to) > 0 else 0
if len(to) == 20:
    expected += to
elif len(to) == 0:
    expected += b'\x00' * 20
expected += struct.pack('<Q', to_present)
expected += value.to_bytes(32, 'big')
# data_offset within tx_rlp:
# We need to figure out where field 5 (data) starts. Use rlp library to inspect.
# Re-decode to find offsets.
decoded = rlp.decode(tx_rlp)
# Find the data field's raw position by re-encoding step by step.
# Simpler: search for the data prefix within tx_rlp.
# But the prefix depends on data length. For our small tests, just locate manually.
# For empty data (b''): RLP byte 0x80, located after the previous fields' bytes.
# For now: cheat. Compute offset by encoding each preceding item.
def field_offset(items, idx):
    # Outer list prefix length:
    payload = b''.join(rlp.encode(it) for it in items)
    if len(payload) < 56:
        prefix_len = 1
    else:
        # Long list: 1 + length-of-length bytes.
        length_bits = (len(payload).bit_length() + 7) // 8
        prefix_len = 1 + length_bits
    offset = prefix_len
    for i in range(idx):
        offset += len(rlp.encode(items[i]))
    # offset is now the start of item idx's RLP encoding (including its prefix).
    # We need the CONTENT offset: skip its RLP prefix.
    item_rlp = rlp.encode(items[idx])
    if len(item_rlp) == 1 and item_rlp[0] < 0x80:
        # Single byte; content offset = full offset.
        content_offset = offset
        content_length = 1
    elif item_rlp[0] < 0xb8:
        # Short string: prefix 1 byte.
        content_offset = offset + 1
        content_length = item_rlp[0] - 0x80
    elif item_rlp[0] < 0xc0:
        # Long string.
        lol = item_rlp[0] - 0xb7
        content_offset = offset + 1 + lol
        content_length = int.from_bytes(item_rlp[1:1+lol], 'big')
    else:
        raise ValueError('unexpected list inside tx')
    return content_offset, content_length

items = [nonce, gas_price, gas_limit, to, value, data, v, r, s]
data_off, data_len = field_offset(items, 5)
expected += struct.pack('<Q', data_off)
expected += struct.pack('<Q', data_len)
expected += struct.pack('<Q', v)
expected += r.to_bytes(32, 'big')
expected += s.to_bytes(32, 'big')

with open(sys.argv[2], 'wb') as f:
    f.write(expected)
" "$in_file" "$exp_file"

  "$ZISKEMU" -e gen-out/zisk_tx_legacy_decode.elf \
    -i "$in_file" -o "$out_file" -n 500000 \
    >"$REPO_ROOT/gen-out/zisk_tx_legacy_decode_${name}.emu.log" 2>&1 || true

  local exp_size; exp_size="$(stat -c%s "$exp_file")"
  local actual expected
  actual="$(xxd -p -l "$exp_size" "$out_file" 2>/dev/null | tr -d '\n')"
  expected="$(xxd -p -l "$exp_size" "$exp_file" 2>/dev/null | tr -d '\n')"

  if [[ "$actual" == "$expected" ]]; then
    printf "  %-26s OK   nonce=%d to=%d B\n" "$name" "$nonce" "$((${#to_hex} / 2))"
    return 0
  else
    printf "  %-26s FAIL\n    expected: %s\n    actual:   %s\n" \
      "$name" "$expected" "$actual"
    return 1
  fi
}

ALICE_ADDR="$(printf 'aa%.0s' $(seq 1 20))"

FAILED=0
# Basic call: send 1 ether to alice, no data
run_case "simple_transfer"    7 1000000000 21000 "$ALICE_ADDR" 1000000000000000000 "" 27 \
  "$(printf '11%.0s' $(seq 1 32))" "$(printf '22%.0s' $(seq 1 32))"  || FAILED=1
# Contract creation (empty to)
run_case "creation"           0 1000000000 100000 "" 0 "6080604052" 27 \
  "$(printf '33%.0s' $(seq 1 32))" "$(printf '44%.0s' $(seq 1 32))"  || FAILED=1
# Larger data
LONG_DATA="$(python3 -c "print(bytes((i & 0xff) for i in range(100)).hex())")"
run_case "with_data"          1 2000000000 50000 "$ALICE_ADDR" 0 "$LONG_DATA" 28 \
  "$(printf '55%.0s' $(seq 1 32))" "$(printf '66%.0s' $(seq 1 32))"  || FAILED=1
# EIP-155 v value
run_case "eip155_v"           100 100000000 30000 "$ALICE_ADDR" 1000000000000000 "" 37 \
  "$(printf '77%.0s' $(seq 1 32))" "$(printf '88%.0s' $(seq 1 32))"  || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: tx_legacy_decode produces the spec-compliant 9-field struct"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
