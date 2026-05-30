#!/usr/bin/env bash
# codegen-zisk-sload-at-block-number-address-check.sh
#
# Number-keyed SLOAD primitive. Mirrors sload_at_block_hash_address
# (#7476) but keyed by block_number.
#
# Output (40 bytes):
#   bytes  0.. 8 : status (0..7 with 5 / 8 reserved)
#   bytes  8..40 : slot value (u256 BE; 0 on missing/absent)
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

echo "==> emit zisk_sload_at_block_number_address ELF"
lake exe codegen --program zisk_sload_at_block_number_address \
  --halt linux93 \
  -o gen-out/zisk_sload_at_block_number_address

REPO_ROOT="$(pwd)"

run_case() {
  local name="$1"; shift
  local mode="$1"; shift
  local target="$1"; shift

  local in_file="$REPO_ROOT/gen-out/zisk_sloadbn_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_sloadbn_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_sloadbn_${name}.expected"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys
import rlp
from Crypto.Hash import keccak

def k256(b):
    h = keccak.new(digest_bits=256); h.update(b); return h.digest()

def hp_encode(nibbles, is_leaf):
    flag = 2 if is_leaf else 0
    if len(nibbles) % 2 == 1:
        flag |= 1
        result = bytes([flag * 0x10 + nibbles[0]])
        nibbles = nibbles[1:]
    else:
        result = bytes([flag * 0x10])
    for i in range(0, len(nibbles), 2):
        result += bytes([nibbles[i] * 0x10 + nibbles[i+1]])
    return result

def leaf_node(path_nibbles, value):
    return rlp.encode([hp_encode(path_nibbles, True), value])

def bytes_to_nibbles(b):
    out = []
    for byte in b:
        out.append(byte >> 4); out.append(byte & 0xf)
    return out

def build_ssz_section(elements):
    n = len(elements)
    if n == 0: return b''
    section = b''
    offset = 4 * n
    for e in elements:
        section += struct.pack('<I', offset); offset += len(e)
    for e in elements: section += e
    return section

def encode_account(nonce, balance, storage_root, code_hash):
    return rlp.encode([nonce, balance, storage_root, code_hash])

def encode_header(number_val, state_root):
    if number_val == 0:
        number_field = b''
    else:
        nbytes = (number_val.bit_length() + 7) // 8
        number_field = number_val.to_bytes(nbytes, 'big')
    fields = [
        b'\\x11'*32, b'\\x22'*32, b'\\x33'*20, state_root, b'\\x55'*32,
        b'\\x66'*32, b'\\x00'*256, b'', number_field, b'\\x83\\xff\\xff\\xff',
        b'', b'\\x83\\x01\\x02\\x03', b'', b'\\x77'*32, b'\\x00'*8,
    ]
    return rlp.encode(fields)

EMPTY_TRIE = bytes.fromhex('56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421')
EMPTY_CODE_HASH = bytes.fromhex('c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470')

def state_trie_one(addr, acct_rlp):
    path = bytes_to_nibbles(k256(addr))
    leaf = leaf_node(path, acct_rlp)
    return k256(leaf), build_ssz_section([leaf])

def storage_trie_one(slot_key_be, value_int):
    if value_int == 0:
        v_short = b''
    else:
        nbytes = (value_int.bit_length() + 7) // 8
        v_short = value_int.to_bytes(nbytes, 'big')
    path = bytes_to_nibbles(k256(slot_key_be))
    leaf = leaf_node(path, rlp.encode(v_short))
    return k256(leaf), build_ssz_section([leaf])

mode = '$mode'
target = int('$target')
ALICE = b'\\xaa' * 20
BOB = b'\\xbb' * 20

def be32(n):
    return n.to_bytes(32, 'big')

if mode == 'value_one':
    slot_idx = be32(0); value = 1
    sr_storage, witness_storage = storage_trie_one(slot_idx, value)
    acct = encode_account(0, 0, sr_storage, EMPTY_CODE_HASH)
    sr, witness_state = state_trie_one(ALICE, acct)
    h0 = encode_header(100, b'\\xee'*32)
    h1 = encode_header(101, sr)
    witness_headers = build_ssz_section([h0, h1])
    addr = ALICE
    expected = struct.pack('<Q', 0) + be32(value)
elif mode == 'value_big_u256':
    slot_idx = be32(7); value = (2**200) - 1
    sr_storage, witness_storage = storage_trie_one(slot_idx, value)
    acct = encode_account(0, 0, sr_storage, EMPTY_CODE_HASH)
    sr, witness_state = state_trie_one(ALICE, acct)
    h0 = encode_header(101, sr)
    witness_headers = build_ssz_section([h0])
    addr = ALICE
    expected = struct.pack('<Q', 0) + be32(value)
elif mode == 'slot_absent':
    slot_idx = be32(99)
    sr_storage, witness_storage = storage_trie_one(be32(7), 42)
    acct = encode_account(0, 0, sr_storage, EMPTY_CODE_HASH)
    sr, witness_state = state_trie_one(ALICE, acct)
    h0 = encode_header(101, sr)
    witness_headers = build_ssz_section([h0])
    addr = ALICE
    expected = struct.pack('<Q', 0) + be32(0)
elif mode == 'empty_storage_root':
    slot_idx = be32(0)
    acct = encode_account(0, 0, EMPTY_TRIE, EMPTY_CODE_HASH)
    sr, witness_state = state_trie_one(ALICE, acct)
    h0 = encode_header(101, sr)
    witness_headers = build_ssz_section([h0])
    witness_storage = b''
    addr = ALICE
    expected = struct.pack('<Q', 0) + be32(0)
elif mode == 'account_absent':
    slot_idx = be32(0)
    acct = encode_account(0, 0, EMPTY_TRIE, EMPTY_CODE_HASH)
    sr, witness_state = state_trie_one(BOB, acct)
    h0 = encode_header(101, sr)
    witness_headers = build_ssz_section([h0])
    witness_storage = b''
    addr = ALICE
    expected = struct.pack('<Q', 0) + be32(0)
elif mode == 'number_miss':
    slot_idx = be32(0)
    sr_storage, witness_storage = storage_trie_one(slot_idx, 5)
    acct = encode_account(0, 0, sr_storage, EMPTY_CODE_HASH)
    sr, witness_state = state_trie_one(ALICE, acct)
    h0 = encode_header(100, sr)
    witness_headers = build_ssz_section([h0])
    addr = ALICE
    expected = struct.pack('<Q', 1) + be32(0)
else:
    raise SystemExit('bad mode: ' + mode)

with open(sys.argv[1], 'wb') as f:
    record = (
        struct.pack('<Q', len(witness_headers))
        + struct.pack('<Q', len(witness_state))
        + struct.pack('<Q', len(witness_storage))
        + struct.pack('<Q', target)
        + slot_idx
        + addr
        + witness_headers
        + witness_state
        + witness_storage
    )
    f.write(record)
    pad = (-len(record)) % 8
    if pad: f.write(b'\\x00' * pad)

with open(sys.argv[2], 'wb') as f:
    f.write(expected)
" "$in_file" "$exp_file"

  "$ZISKEMU" -e gen-out/zisk_sload_at_block_number_address.elf \
    -i "$in_file" -o "$out_file" -n 6000000 \
    >"$REPO_ROOT/gen-out/zisk_sloadbn_${name}.emu.log" 2>&1 || true

  local exp_size; exp_size="$(stat -c%s "$exp_file")"
  local actual expected
  actual="$(xxd -p -l "$exp_size" "$out_file" 2>/dev/null | tr -d '\n')"
  expected="$(xxd -p -l "$exp_size" "$exp_file" 2>/dev/null | tr -d '\n')"

  if [[ "$actual" == "$expected" ]]; then
    printf "  %-36s OK   %d bytes match\n" "$name" "$exp_size"
    return 0
  else
    printf "  %-36s FAIL\n    expected: %s\n    actual:   %s\n" \
      "$name" "$expected" "$actual"
    return 1
  fi
}

FAILED=0
run_case "value_one"                       value_one 101 || FAILED=1
run_case "value_big_u256"                  value_big_u256 101 || FAILED=1
run_case "slot_absent_returns_zero"        slot_absent 101 || FAILED=1
run_case "empty_storage_root_returns_zero" empty_storage_root 101 || FAILED=1
run_case "account_absent_returns_zero"     account_absent 101 || FAILED=1
run_case "number_not_in_section"           number_miss 999 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: sload_at_block_number_address end-to-end"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
