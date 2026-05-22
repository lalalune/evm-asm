#!/usr/bin/env bash
# codegen-zisk-tx-eip4844-decode-check.sh -- PR-K45.
#
# Decode all 14 fields of an EIP-4844 (type-3) blob tx inner body
# into a 248-byte struct. Cross-validated against Python's RLP
# encoder. Caller is expected to have stripped the 0x03 type byte
# beforehand (PR-K40 tx_type_dispatch gives the offset).
#
# Note: max_fee_per_blob_gas is stored as u64 (rejects > 8 B BE);
# callers needing the full u256 can re-extract via
# rlp_field_to_u256_be at field index 9.
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

echo "==> emit zisk_tx_eip4844_decode ELF"
lake exe codegen --program zisk_tx_eip4844_decode --halt linux93 \
  -o gen-out/zisk_tx_eip4844_decode

REPO_ROOT="$(pwd)"

# run_case <name> <chain_id> <nonce> <max_priority> <max_fee> <gas_limit>
#         <to_hex> <value> <data_hex>
#         <access_list_json> <max_fee_per_blob_gas>
#         <blob_hashes_json>
#         <y_parity> <r_hex> <s_hex>
#
# blob_hashes_json: list of 32-byte hex strings, e.g. '["aabb..", "ccdd.."]'
run_case() {
  local name="$1"
  local chain_id="$2" nonce="$3" max_priority="$4" max_fee="$5" gas_limit="$6"
  local to_hex="$7" value="$8" data_hex="$9"
  local access_list_json="${10}" max_blob_fee="${11}"
  local blob_hashes_json="${12}"
  local y_parity="${13}" r_hex="${14}" s_hex="${15}"

  local in_file="$REPO_ROOT/gen-out/zisk_tx_eip4844_decode_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_tx_eip4844_decode_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_tx_eip4844_decode_${name}.expected"

  uv run --directory execution-specs --quiet python3 -c "
import json, struct, sys
import rlp

chain_id = $chain_id
nonce = $nonce
max_priority = $max_priority
max_fee = $max_fee
gas_limit = $gas_limit
to = bytes.fromhex('$to_hex')
value = $value
data = bytes.fromhex('$data_hex')
access_list_raw = json.loads('''$access_list_json''')
max_blob_fee = $max_blob_fee
blob_hashes_raw = json.loads('''$blob_hashes_json''')
y_parity = $y_parity
r = int.from_bytes(bytes.fromhex('$r_hex'), 'big')
s = int.from_bytes(bytes.fromhex('$s_hex'), 'big')

access_list = []
for entry in access_list_raw:
    addr_hex, slots_hex = entry
    addr = bytes.fromhex(addr_hex)
    slots = [bytes.fromhex(k) for k in slots_hex]
    access_list.append([addr, slots])

blob_hashes = [bytes.fromhex(h) for h in blob_hashes_raw]

inner_rlp = rlp.encode([
    chain_id, nonce, max_priority, max_fee, gas_limit,
    to, value, data, access_list,
    max_blob_fee, blob_hashes,
    y_parity, r, s,
])

with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(inner_rlp)))
    f.write(inner_rlp)
    pad = (-(8 + len(inner_rlp))) % 8
    if pad:
        f.write(b'\x00' * pad)

# Expected: status u64 LE + 248-byte struct.
expected = struct.pack('<Q', 0)
expected += struct.pack('<Q', chain_id)
expected += struct.pack('<Q', nonce)
expected += max_priority.to_bytes(32, 'big')
expected += max_fee.to_bytes(32, 'big')
expected += struct.pack('<Q', gas_limit)
to_present = 1 if len(to) > 0 else 0
if len(to) == 20:
    expected += to
elif len(to) == 0:
    expected += b'\x00' * 20
expected += struct.pack('<I', to_present)
expected += value.to_bytes(32, 'big')

items = [
    chain_id, nonce, max_priority, max_fee, gas_limit,
    to, value, data, access_list,
    max_blob_fee, blob_hashes,
    y_parity, r, s,
]
def field_offset(items, idx):
    payload = b''.join(rlp.encode(it) for it in items)
    if len(payload) < 56:
        prefix_len = 1
    else:
        length_bits = (len(payload).bit_length() + 7) // 8
        prefix_len = 1 + length_bits
    offset = prefix_len
    for i in range(idx):
        offset += len(rlp.encode(items[i]))
    item_rlp = rlp.encode(items[idx])
    if len(item_rlp) == 1 and item_rlp[0] < 0x80:
        return offset, 1
    elif item_rlp[0] < 0xb8:
        return offset + 1, item_rlp[0] - 0x80
    elif item_rlp[0] < 0xc0:
        lol = item_rlp[0] - 0xb7
        return (offset + 1 + lol,
                int.from_bytes(item_rlp[1:1+lol], 'big'))
    else:
        return offset, len(item_rlp)

data_off, data_len = field_offset(items, 7)
al_off, al_len = field_offset(items, 8)
bh_off, bh_len = field_offset(items, 10)
expected += struct.pack('<I', data_off)
expected += struct.pack('<I', data_len)
expected += struct.pack('<I', al_off)
expected += struct.pack('<I', al_len)
expected += struct.pack('<Q', max_blob_fee)
expected += struct.pack('<I', bh_off)
expected += struct.pack('<I', bh_len)
expected += struct.pack('<Q', y_parity)
expected += r.to_bytes(32, 'big')
expected += s.to_bytes(32, 'big')

with open(sys.argv[2], 'wb') as f:
    f.write(expected)
" "$in_file" "$exp_file"

  "$ZISKEMU" -e gen-out/zisk_tx_eip4844_decode.elf \
    -i "$in_file" -o "$out_file" -n 500000 \
    >"$REPO_ROOT/gen-out/zisk_tx_eip4844_decode_${name}.emu.log" 2>&1 || true

  local exp_size; exp_size="$(stat -c%s "$exp_file")"
  local actual expected
  actual="$(xxd -p -l "$exp_size" "$out_file" 2>/dev/null | tr -d '\n')"
  expected="$(xxd -p -l "$exp_size" "$exp_file" 2>/dev/null | tr -d '\n')"

  if [[ "$actual" == "$expected" ]]; then
    printf "  %-30s OK   nonce=%d blob_hashes=%d blob_fee=%d\n" \
      "$name" "$nonce" "$(python3 -c "import json; print(len(json.loads('''$blob_hashes_json''')))")" \
      "$max_blob_fee"
    return 0
  else
    printf "  %-30s FAIL\n    expected: %s\n    actual:   %s\n" \
      "$name" "$expected" "$actual"
    return 1
  fi
}

ALICE="$(printf 'aa%.0s' $(seq 1 20))"
BOB="$(printf 'bb%.0s' $(seq 1 20))"
R1="$(printf '11%.0s' $(seq 1 32))"
S1="$(printf '22%.0s' $(seq 1 32))"
R2="$(printf '33%.0s' $(seq 1 32))"
S2="$(printf '44%.0s' $(seq 1 32))"
K1="$(printf '55%.0s' $(seq 1 32))"
# Blob versioned hashes (32 B each, all start with 0x01 per spec)
H1="01$(printf 'aa%.0s' $(seq 1 31))"
H2="01$(printf 'bb%.0s' $(seq 1 31))"
H3="01$(printf 'cc%.0s' $(seq 1 31))"

FAILED=0
# One blob, empty access list
run_case "one_blob" \
  1 7 1000000000 2000000000 21000 \
  "$ALICE" 1000000000000000000 "" \
  "[]" 1 \
  "[\"$H1\"]" \
  0 "$R1" "$S1" || FAILED=1

# Multiple blobs (Cancun cap is 6)
run_case "three_blobs" \
  1 9 100 200 50000 \
  "$BOB" 100 "deadbeef" \
  "[]" 1000000000 \
  "[\"$H1\", \"$H2\", \"$H3\"]" \
  1 "$R2" "$S2" || FAILED=1

# Six blobs (Cancun-era max)
run_case "six_blobs" \
  1 0 1 2 100000 \
  "$BOB" 0 "" \
  "[]" 1 \
  "[\"$H1\", \"$H1\", \"$H2\", \"$H2\", \"$H3\", \"$H3\"]" \
  0 "$R1" "$S2" || FAILED=1

# With access list
run_case "blobs_and_access" \
  1 3 1 2 60000 \
  "$BOB" 1 "" \
  "[[\"$ALICE\", [\"$K1\"]]]" 5 \
  "[\"$H1\", \"$H2\"]" \
  1 "$R1" "$S1" || FAILED=1

# Big blob_fee (still u64-fit)
run_case "big_blob_fee_u64" \
  1 5 1 1 30000 \
  "$BOB" 0 "" \
  "[]" 18446744073709551615 \
  "[\"$H1\"]" \
  0 "$R1" "$S1" || FAILED=1

# Long data path
LONGER_DATA="$(python3 -c "print(bytes((i & 0xff) for i in range(300)).hex())")"
run_case "long_data" \
  1 100 2 3 1000000 \
  "$ALICE" 0 "$LONGER_DATA" \
  "[]" 7 \
  "[\"$H1\", \"$H2\"]" \
  0 "$R1" "$S1" || FAILED=1

# Big chain_id
run_case "big_chain_id" \
  17000 42 3 4 100000 \
  "$ALICE" 1 "" \
  "[]" 1 \
  "[\"$H1\"]" \
  1 "$R1" "$S1" || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: tx_eip4844_decode produces the spec-compliant 14-field struct"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
