#!/usr/bin/env bash
# codegen-zisk-tx-eip1559-decode-check.sh -- PR-K41.
#
# Decode all 12 fields of an EIP-1559 (type-2) tx inner body
# into a 252-byte struct. Cross-validated against Python's RLP
# encoder. Caller is expected to have stripped the 0x02 type
# byte beforehand (PR-K40 tx_type_dispatch gives the offset).
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

echo "==> emit zisk_tx_eip1559_decode ELF"
lake exe codegen --program zisk_tx_eip1559_decode --halt linux93 \
  -o gen-out/zisk_tx_eip1559_decode

REPO_ROOT="$(pwd)"

# run_case <name> <chain_id> <nonce> <max_priority> <max_fee> <gas_limit>
#         <to_hex> <value> <data_hex> <access_list_json> <y_parity>
#         <r_hex> <s_hex>
#
# access_list_json: JSON-list-of-pairs as understood by the embedded
# Python (e.g. '[]' for empty, or
#   '[["aaaa...", ["11..", "22.."]], ...]').
run_case() {
  local name="$1"
  local chain_id="$2" nonce="$3" max_priority="$4" max_fee="$5" gas_limit="$6"
  local to_hex="$7" value="$8" data_hex="$9"
  local access_list_json="${10}" y_parity="${11}"
  local r_hex="${12}" s_hex="${13}"

  local in_file="$REPO_ROOT/gen-out/zisk_tx_eip1559_decode_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_tx_eip1559_decode_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_tx_eip1559_decode_${name}.expected"

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
y_parity = $y_parity
r = int.from_bytes(bytes.fromhex('$r_hex'), 'big')
s = int.from_bytes(bytes.fromhex('$s_hex'), 'big')

# access_list elements: [address(20B hex), [storage_key1(32B hex), ...]]
access_list = []
for entry in access_list_raw:
    addr_hex, slots_hex = entry
    addr = bytes.fromhex(addr_hex)
    slots = [bytes.fromhex(k) for k in slots_hex]
    access_list.append([addr, slots])

inner_rlp = rlp.encode([
    chain_id, nonce, max_priority, max_fee, gas_limit,
    to, value, data, access_list, y_parity, r, s,
])

with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(inner_rlp)))
    f.write(inner_rlp)
    pad = (-(8 + len(inner_rlp))) % 8
    if pad:
        f.write(b'\x00' * pad)

# Expected: status u64 LE + 248-byte struct (ziskemu output caps at 256B).
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

# Compute data/access_list offsets within inner_rlp. Semantics mirror
# rlp_list_nth_item: byte-string items return content offset/length
# (prefix stripped); LIST items return the *whole* encoded item
# (offset = item_start, length = full encoded length incl. prefix).
items = [
    chain_id, nonce, max_priority, max_fee, gas_limit,
    to, value, data, access_list, y_parity, r, s,
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
        # List item: whole encoded extent.
        return offset, len(item_rlp)

data_off, data_len = field_offset(items, 7)
al_off, al_len = field_offset(items, 8)
expected += struct.pack('<Q', data_off)
expected += struct.pack('<Q', data_len)
expected += struct.pack('<Q', al_off)
expected += struct.pack('<Q', al_len)
expected += struct.pack('<Q', y_parity)
expected += r.to_bytes(32, 'big')
expected += s.to_bytes(32, 'big')

with open(sys.argv[2], 'wb') as f:
    f.write(expected)
" "$in_file" "$exp_file"

  "$ZISKEMU" -e gen-out/zisk_tx_eip1559_decode.elf \
    -i "$in_file" -o "$out_file" -n 500000 \
    >"$REPO_ROOT/gen-out/zisk_tx_eip1559_decode_${name}.emu.log" 2>&1 || true

  local exp_size; exp_size="$(stat -c%s "$exp_file")"
  local actual expected
  actual="$(xxd -p -l "$exp_size" "$out_file" 2>/dev/null | tr -d '\n')"
  expected="$(xxd -p -l "$exp_size" "$exp_file" 2>/dev/null | tr -d '\n')"

  if [[ "$actual" == "$expected" ]]; then
    printf "  %-30s OK   nonce=%d to_len=%d al=%s\n" \
      "$name" "$nonce" "$((${#to_hex} / 2))" \
      "$([[ "$access_list_json" == "[]" ]] && echo "[]" || echo "<filled>")"
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
K2="$(printf '66%.0s' $(seq 1 32))"

FAILED=0
# Simple ether transfer, empty access list, no data
run_case "simple_transfer" \
  1 7 1000000000 2000000000 21000 \
  "$ALICE" 1000000000000000000 "" \
  "[]" 0 "$R1" "$S1" || FAILED=1

# Contract creation (empty to)
run_case "creation" \
  1 0 1500000000 3000000000 100000 \
  "" 0 "6080604052" \
  "[]" 1 "$R2" "$S2" || FAILED=1

# With non-trivial data
LONG_DATA="$(python3 -c "print(bytes((i & 0xff) for i in range(120)).hex())")"
run_case "with_data" \
  10 1 100 5000000000 50000 \
  "$ALICE" 0 "$LONG_DATA" \
  "[]" 0 "$R1" "$S1" || FAILED=1

# Non-empty access list (one entry)
run_case "with_access_list_1" \
  1 5 2000000000 4000000000 60000 \
  "$BOB" 100 "" \
  "[[\"$ALICE\", [\"$K1\"]]]" 1 "$R1" "$S2" || FAILED=1

# Non-empty access list (two entries, multiple slots)
run_case "with_access_list_2" \
  1 9 1 2 80000 \
  "$BOB" 999999999999 "deadbeef" \
  "[[\"$ALICE\", [\"$K1\", \"$K2\"]], [\"$BOB\", [\"$K1\"]]]" 0 "$R2" "$S1" || FAILED=1

# Large chain_id (Holesky-ish)
run_case "big_chain_id" \
  17000 42 3 4 100000 \
  "$ALICE" 1 "" \
  "[]" 1 "$R1" "$S1" || FAILED=1

# Max values
run_case "max_fields" \
  1 1844674407370955160 1000 1000000 30000000 \
  "$ALICE" 115792089237316195423570985008687907853269984665640564039457584007913129639935 "" \
  "[]" 1 "$R2" "$S2" || FAILED=1

# Long data (>56 bytes, triggers long-string RLP prefix)
LONGER_DATA="$(python3 -c "print(bytes((i & 0xff) for i in range(300)).hex())")"
run_case "long_data" \
  1 100 2 3 1000000 \
  "$ALICE" 0 "$LONGER_DATA" \
  "[]" 0 "$R1" "$S1" || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: tx_eip1559_decode produces the spec-compliant 12-field struct"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
