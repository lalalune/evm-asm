#!/usr/bin/env bash
# codegen-zisk-block-validate-transactions-root-two-tx-check.sh -- PR-K171.
#
# End-to-end transactions_root validation for 2-tx blocks: extract
# header.field[4] (via K20), recompute the expected root via K170
# (mpt_two_leaf_root_indexed), and compare 32 B.
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

echo "==> emit zisk_block_validate_transactions_root_two_tx ELF"
lake exe codegen --program zisk_block_validate_transactions_root_two_tx --halt linux93 \
  -o gen-out/zisk_block_validate_transactions_root_two_tx

REPO_ROOT="$(pwd)"

# run_case <name> <tx0_hex> <tx1_hex> <override_root_hex_or_empty> <expected_status> <expected_valid>
#
# override_root_hex_or_empty:
#   ""              -- use the correct computed root in the header
#   "<32B hex>"     -- splice that into the header's field 4 instead
#   "shortroot"     -- splice a 16-byte value into field 4 to trigger size_fail
#   "garbage"       -- emit a malformed RLP header (single 0x00 byte) for parse_fail
run_case() {
  local name="$1" tx0="$2" tx1="$3" override="$4"
  local exp_status="$5" exp_valid="$6"

  local in_file="$REPO_ROOT/gen-out/zisk_block_validate_transactions_root_two_tx_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_block_validate_transactions_root_two_tx_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys, rlp
try:
    from Crypto.Hash import keccak
    def keccak256(b):
        h = keccak.new(digest_bits=256); h.update(b); return h.digest()
except Exception:
    import sha3
    def keccak256(b): return sha3.keccak_256(b).digest()

tx0 = bytes.fromhex('$tx0')
tx1 = bytes.fromhex('$tx1')
override = '$override'

# --- Compute correct transactions_root with the same algorithm K170 uses.
def hp_leaf(nibbles, value):
    flag = 2 + (len(nibbles) & 1)
    hp = bytearray()
    if len(nibbles) % 2 == 1:
        hp.append((flag << 4) | nibbles[0]); i = 1
    else:
        hp.append(flag << 4); i = 0
    while i < len(nibbles):
        hp.append((nibbles[i] << 4) | nibbles[i+1]); i += 2
    return rlp.encode([bytes(hp), value])

def slot_ref(node_rlp):
    if len(node_rlp) < 32:
        return node_rlp
    return b'\\xa0' + keccak256(node_rlp)

leaf_0 = hp_leaf([0], tx0)   # key rlp(0)=0x80 -> nibbles [8,0]
leaf_1 = hp_leaf([1], tx1)   # key rlp(1)=0x01 -> nibbles [0,1]
slots = [b'\\x80'] * 17
slots[8] = slot_ref(leaf_0)
slots[0] = slot_ref(leaf_1)
payload = b''.join(slots)
n = len(payload)
if n < 56:
    prefix = bytes([0xc0 + n])
else:
    nb = n.to_bytes((n.bit_length() + 7) // 8, 'big')
    prefix = bytes([0xf7 + len(nb)]) + nb
branch_node_rlp = prefix + payload
correct_root = keccak256(branch_node_rlp)

# --- Build a synthetic block header with the chosen field 4 contents.
parent_hash    = b'\\x11' * 32
ommers_hash    = b'\\x22' * 32
beneficiary    = b'\\x33' * 20
state_root     = b'\\x44' * 32
receipts_root  = b'\\x66' * 32
logs_bloom     = b'\\x00' * 256
difficulty     = b''
number         = b'\\x01'
gas_limit      = b'\\x83\\xff\\xff\\xff'  # 0x83ffffff (24-bit) is just an example
gas_used       = b''
timestamp      = b'\\x83\\x01\\x02\\x03'  # arbitrary
extra_data     = b''
prev_randao    = b'\\x77' * 32
nonce          = b'\\x00' * 8

if override == 'garbage':
    header_rlp = b'\\x00'   # not a valid RLP list -- triggers parse_fail
else:
    if override == '':
        field4 = correct_root
    elif override == 'shortroot':
        field4 = b'\\x55' * 16
    else:
        field4 = bytes.fromhex(override)
    header_fields = [
        parent_hash, ommers_hash, beneficiary, state_root,
        field4, receipts_root, logs_bloom,
        difficulty, number, gas_limit, gas_used, timestamp,
        extra_data, prev_randao, nonce,
    ]
    header_rlp = rlp.encode(header_fields)

with open(sys.argv[1], 'wb') as f:
    # ziskemu maps file bytes to INPUT_ADDR+8; prologue reads
    # header_rlp_len from offset 8 (= file byte 0), tx0_len from
    # offset 16, tx1_len from offset 24, and the payload from
    # offset 32 onward.
    record = struct.pack('<Q', len(header_rlp)) + \
             struct.pack('<Q', len(tx0)) + \
             struct.pack('<Q', len(tx1)) + \
             header_rlp + tx0 + tx1
    f.write(record)
    pad = (-len(record)) % 8
    if pad: f.write(b'\x00' * pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_block_validate_transactions_root_two_tx.elf \
    -i "$in_file" -o "$out_file" -n 5000000 \
    >"$REPO_ROOT/gen-out/zisk_block_validate_transactions_root_two_tx_${name}.emu.log" 2>&1 || true

  local status_le; status_le="$(xxd -p -l 8 "$out_file" | tr -d '\n')"
  local valid_le;  valid_le="$( dd if="$out_file" bs=1 skip=8 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local status valid
  status="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$status_le'))[0])")"
  valid="$( python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$valid_le'))[0])")"

  if [[ "$status" == "$exp_status" && "$valid" == "$exp_valid" ]]; then
    printf "  %-30s OK   status=%s valid=%s\n" "$name" "$status" "$valid"
    return 0
  else
    printf "  %-30s FAIL status=%s (exp %s) valid=%s (exp %s)\n" \
      "$name" "$status" "$exp_status" "$valid" "$exp_valid"
    return 1
  fi
}

TX_A="f8500184ee6b280082520894aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa881bc16d674ec80000801ba01111111111111111111111111111111111111111111111111111111111111111a02222222222222222222222222222222222222222222222222222222222222222"
TX_B="f8500284ee6b280082520894bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb881bc16d674ec80000801ba03333333333333333333333333333333333333333333333333333333333333333a04444444444444444444444444444444444444444444444444444444444444444"

WRONG_ROOT="ffeeddccbbaa99887766554433221100ffeeddccbbaa99887766554433221100"

FAILED=0
# Correct claimed root + 2 long-tx leaves -> is_valid=1
run_case "match_two_legacy"     "$TX_A" "$TX_B" ""           0 1 || FAILED=1
# Correct claimed root + 2 short values (inline slot ref path)
run_case "match_two_short"      "01"    "02"    ""           0 1 || FAILED=1
# Wrong claimed root + correct 2-tx -> is_valid=0 (no error code)
run_case "mismatch_wrong_root"  "$TX_A" "$TX_B" "$WRONG_ROOT" 0 0 || FAILED=1
# Header has a 16-byte field 4 -> size_fail (status=2, valid=0)
run_case "size_fail_short"      "$TX_A" "$TX_B" "shortroot"  2 0 || FAILED=1
# Header is a single 0x00 byte -> parse_fail (status=1, valid=0)
run_case "parse_fail_garbage"   "$TX_A" "$TX_B" "garbage"    1 0 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: block_validate_transactions_root_two_tx accepts matching roots and rejects others"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
