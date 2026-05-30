#!/usr/bin/env bash
# codegen-zisk-sload-at-block-hash-address-check.sh
#
# Hash-keyed SLOAD. From (block_hash, address, slot_idx,
# witness.headers, witness.state, witness.storage), return
# the u256 value SLOAD(slot) would push when executed
# against the storage trie of `address` at the block named
# by block_hash.
#
# Per spec, returns 0 for: missing account, EMPTY_TRIE storage_root,
# missing slot.
#
# Output (40 bytes):
#   bytes  0.. 8 : status (0 / 1 / 2 / 3 / 4 / 6 / 7)
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

echo "==> emit zisk_sload_at_block_hash_address ELF"
lake exe codegen --program zisk_sload_at_block_hash_address \
  --halt linux93 \
  -o gen-out/zisk_sload_at_block_hash_address

REPO_ROOT="$(pwd)"

run_case() {
  local name="$1"; shift
  local mode="$1"; shift

  local in_file="$REPO_ROOT/gen-out/zisk_sloadbh_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_sloadbh_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_sloadbh_${name}.expected"

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

def encode_header(state_root):
    fields = [
        b'\\x11'*32, b'\\x22'*32, b'\\x33'*20, state_root, b'\\x55'*32,
        b'\\x66'*32, b'\\x00'*256, b'', b'\\x01', b'\\x83\\xff\\xff\\xff',
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
    # MPT key is keccak(slot_key_be). Value is rlp-encoded big-endian-shortest u256.
    if value_int == 0:
        v_short = b''
    else:
        nbytes = (value_int.bit_length() + 7) // 8
        v_short = value_int.to_bytes(nbytes, 'big')
    path = bytes_to_nibbles(k256(slot_key_be))
    leaf = leaf_node(path, rlp.encode(v_short))
    return k256(leaf), build_ssz_section([leaf])

mode = '$mode'
parts = [
$(for arg in "$@"; do printf '  %s,\n' "\"$arg\""; done)
]
ALICE = b'\\xaa' * 20
BOB = b'\\xbb' * 20

def be32(n):
    return n.to_bytes(32, 'big')

if mode == 'value_one':
    slot_idx = be32(0)
    value = 1
    sr_storage, witness_storage = storage_trie_one(slot_idx, value)
    acct = encode_account(0, 0, sr_storage, EMPTY_CODE_HASH)
    sr, witness_state = state_trie_one(ALICE, acct)
    h0 = encode_header(sr); witness_headers = build_ssz_section([h0])
    block_hash = k256(h0); addr = ALICE
    expected = struct.pack('<Q', 0) + be32(value)
elif mode == 'value_big_u256':
    slot_idx = be32(7)
    value = (2**200) - 1
    sr_storage, witness_storage = storage_trie_one(slot_idx, value)
    acct = encode_account(0, 0, sr_storage, EMPTY_CODE_HASH)
    sr, witness_state = state_trie_one(ALICE, acct)
    h0 = encode_header(sr); witness_headers = build_ssz_section([h0])
    block_hash = k256(h0); addr = ALICE
    expected = struct.pack('<Q', 0) + be32(value)
elif mode == 'slot_zero_explicit':
    slot_idx = be32(1)
    value = 0
    sr_storage, witness_storage = storage_trie_one(slot_idx, value)
    acct = encode_account(0, 0, sr_storage, EMPTY_CODE_HASH)
    sr, witness_state = state_trie_one(ALICE, acct)
    h0 = encode_header(sr); witness_headers = build_ssz_section([h0])
    block_hash = k256(h0); addr = ALICE
    expected = struct.pack('<Q', 0) + be32(0)
elif mode == 'slot_absent':
    # Slot we look up is not in trie -> SLOAD = 0.
    slot_idx = be32(99)
    sr_storage, witness_storage = storage_trie_one(be32(7), 42)
    acct = encode_account(0, 0, sr_storage, EMPTY_CODE_HASH)
    sr, witness_state = state_trie_one(ALICE, acct)
    h0 = encode_header(sr); witness_headers = build_ssz_section([h0])
    block_hash = k256(h0); addr = ALICE
    expected = struct.pack('<Q', 0) + be32(0)
elif mode == 'empty_storage_root':
    # Account exists but storage_root == EMPTY_TRIE -> SLOAD = 0.
    slot_idx = be32(0)
    acct = encode_account(0, 0, EMPTY_TRIE, EMPTY_CODE_HASH)
    sr, witness_state = state_trie_one(ALICE, acct)
    h0 = encode_header(sr); witness_headers = build_ssz_section([h0])
    witness_storage = b''
    block_hash = k256(h0); addr = ALICE
    expected = struct.pack('<Q', 0) + be32(0)
elif mode == 'account_absent':
    # Lookup ALICE, only BOB in trie -> SLOAD = 0.
    slot_idx = be32(0)
    acct = encode_account(0, 0, EMPTY_TRIE, EMPTY_CODE_HASH)
    sr, witness_state = state_trie_one(BOB, acct)
    h0 = encode_header(sr); witness_headers = build_ssz_section([h0])
    witness_storage = b''
    block_hash = k256(h0); addr = ALICE
    expected = struct.pack('<Q', 0) + be32(0)
elif mode == 'block_hash_miss':
    slot_idx = be32(0)
    sr_storage, witness_storage = storage_trie_one(slot_idx, 5)
    acct = encode_account(0, 0, sr_storage, EMPTY_CODE_HASH)
    sr, witness_state = state_trie_one(ALICE, acct)
    h0 = encode_header(sr); witness_headers = build_ssz_section([h0])
    block_hash = b'\\xee' * 32; addr = ALICE
    expected = struct.pack('<Q', 1) + be32(0)
else:
    raise SystemExit('bad mode: ' + mode)

with open(sys.argv[1], 'wb') as f:
    record = (
        struct.pack('<Q', len(witness_headers))
        + struct.pack('<Q', len(witness_state))
        + struct.pack('<Q', len(witness_storage))
        + block_hash
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

  "$ZISKEMU" -e gen-out/zisk_sload_at_block_hash_address.elf \
    -i "$in_file" -o "$out_file" -n 6000000 \
    >"$REPO_ROOT/gen-out/zisk_sloadbh_${name}.emu.log" 2>&1 || true

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
run_case "value_one"                  value_one || FAILED=1
run_case "value_big_u256"             value_big_u256 || FAILED=1
run_case "slot_zero_explicit"         slot_zero_explicit || FAILED=1
run_case "slot_absent_returns_zero"   slot_absent || FAILED=1
run_case "empty_storage_root"         empty_storage_root || FAILED=1
run_case "account_absent_returns_zero" account_absent || FAILED=1
run_case "block_hash_miss"            block_hash_miss || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: sload_at_block_hash_address end-to-end"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
