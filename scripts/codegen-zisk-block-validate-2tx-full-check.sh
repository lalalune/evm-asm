#!/usr/bin/env bash
# codegen-zisk-block-validate-2tx-full-check.sh -- PR-K176.
#
# Full validation of a 2-tx block: parent_hash + number+1 + ts +
# gas_limit (K174) AND transactions_root MPT match (K171).
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

echo "==> emit zisk_block_validate_2tx_full ELF"
lake exe codegen --program zisk_block_validate_2tx_full --halt linux93 \
  -o gen-out/zisk_block_validate_2tx_full

REPO_ROOT="$(pwd)"

# run_case <name> <break_pair 0/1> <break_tx_root 0/1> <exp_status> <exp_valid>
run_case() {
  local name="$1" break_pair="$2" break_tx_root="$3" exp_status="$4" exp_valid="$5"

  local in_file="$REPO_ROOT/gen-out/zisk_block_validate_2tx_full_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_block_validate_2tx_full_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys, rlp
try:
    from Crypto.Hash import keccak
    def keccak256(b):
        h = keccak.new(digest_bits=256); h.update(b); return h.digest()
except Exception:
    import sha3
    def keccak256(b): return sha3.keccak_256(b).digest()

def u_be(n):
    if n == 0: return b''
    return n.to_bytes((n.bit_length() + 7) // 8, 'big')

break_pair = $break_pair == 1
break_tx_root = $break_tx_root == 1

tx0 = bytes.fromhex('f8500184ee6b280082520894aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa881bc16d674ec80000801ba01111111111111111111111111111111111111111111111111111111111111111a02222222222222222222222222222222222222222222222222222222222222222')
tx1 = bytes.fromhex('f8500284ee6b280082520894bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb881bc16d674ec80000801ba03333333333333333333333333333333333333333333333333333333333333333a04444444444444444444444444444444444444444444444444444444444444444')

# Compute the correct transactions_root for these 2 txs.
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

leaf_0 = hp_leaf([0], tx0)
leaf_1 = hp_leaf([1], tx1)
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
correct_tx_root = keccak256(prefix + payload)

# Make parent first; child's parent_hash is computed from keccak(parent_rlp).
parent_fields = [
    b'\\xa1'*32, b'\\xa2'*32, b'\\xa3'*20, b'\\xa4'*32, b'\\xa5'*32,
    b'\\xa6'*32, b'\\x00'*256, b'', u_be(100), u_be(30000000),
    b'\\x82\\x02\\x00', u_be(1000), b'', b'\\xa7'*32, b'\\x00'*8,
    b'\\x82\\x12\\x34',
]
parent_rlp = rlp.encode(parent_fields)
parent_hash = keccak256(parent_rlp)

if break_tx_root:
    field4 = b'\\xff' * 32
else:
    field4 = correct_tx_root

# Break pair by skipping number (child.number = parent.number + 2).
if break_pair:
    child_num = 102
else:
    child_num = 101

child_fields = [
    parent_hash, b'\\xb2'*32, b'\\xb3'*20, b'\\xb4'*32, field4,
    b'\\xb6'*32, b'\\x00'*256, b'', u_be(child_num), u_be(30000000),
    b'\\x82\\x02\\x00', u_be(1001), b'', b'\\xb7'*32, b'\\x00'*8,
    b'\\x82\\x12\\x34',
]
child_rlp = rlp.encode(child_fields)

with open(sys.argv[1], 'wb') as f:
    record = struct.pack('<Q', len(parent_rlp)) + \
             struct.pack('<Q', len(child_rlp)) + \
             struct.pack('<Q', len(tx0)) + \
             struct.pack('<Q', len(tx1)) + \
             parent_rlp + child_rlp + tx0 + tx1
    f.write(record)
    pad = (-len(record)) % 8
    if pad: f.write(b'\x00' * pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_block_validate_2tx_full.elf \
    -i "$in_file" -o "$out_file" -n 10000000 \
    >"$REPO_ROOT/gen-out/zisk_block_validate_2tx_full_${name}.emu.log" 2>&1 || true

  local status_le; status_le="$(xxd -p -l 8 "$out_file" | tr -d '\n')"
  local valid_le;  valid_le="$( dd if="$out_file" bs=1 skip=8 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local status valid
  status="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$status_le'))[0])")"
  valid="$( python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$valid_le'))[0])")"

  if [[ "$status" == "$exp_status" && "$valid" == "$exp_valid" ]]; then
    printf "  %-28s OK   status=%s valid=%s\n" "$name" "$status" "$valid"
    return 0
  else
    printf "  %-28s FAIL status=%s/exp%s valid=%s/exp%s\n" \
      "$name" "$status" "$exp_status" "$valid" "$exp_valid"
    return 1
  fi
}

FAILED=0
# Everything correct -> valid=1
run_case "all_match"             0 0 0 1 || FAILED=1
# Pair check fails (number skip) -> valid=0
run_case "fail_pair_number_skip" 1 0 0 0 || FAILED=1
# Tx-root check fails -> valid=0
run_case "fail_tx_root_mismatch" 0 1 0 0 || FAILED=1
# Both broken -> still valid=0 (pair check fires first)
run_case "fail_both"             1 1 0 0 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: block_validate_2tx_full enforces pair + tx_root invariants"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
