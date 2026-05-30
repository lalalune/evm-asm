#!/usr/bin/env bash
# codegen-zisk-account-storage-walkable-at-state-root-check.sh
#
# Fused precondition: walk to account.storage_root, then
# check storage_root is in witness.storage.
#
# Output (16 bytes):
#   bytes  0.. 8 : status (0..3)
#   bytes  8..16 : walkable (u64; 0 or 1)
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

echo "==> emit zisk_account_storage_walkable_at_state_root ELF"
lake exe codegen --program zisk_account_storage_walkable_at_state_root \
  --halt linux93 \
  -o gen-out/zisk_account_storage_walkable_at_state_root

REPO_ROOT="$(pwd)"

run_case() {
  local name="$1"; shift
  local mode="$1"; shift

  local in_file="$REPO_ROOT/gen-out/zisk_aswr_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_aswr_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_aswr_${name}.expected"

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

EMPTY_TRIE = bytes.fromhex('56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421')
EMPTY_CODE_HASH = bytes.fromhex('c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470')

def state_trie_one(addr, acct_rlp):
    path = bytes_to_nibbles(k256(addr))
    leaf = leaf_node(path, acct_rlp)
    return k256(leaf), build_ssz_section([leaf])

def storage_trie_one(slot_be, val_be):
    path = bytes_to_nibbles(k256(slot_be))
    leaf = leaf_node(path, rlp.encode(val_be.lstrip(b'\\x00')))
    return k256(leaf), build_ssz_section([leaf])

mode = '$mode'
ALICE = b'\\xaa' * 20
BOB = b'\\xbb' * 20

if mode == 'walkable_present':
    # Contract with populated storage, full storage trie in witness.
    sr_storage, witness_storage = storage_trie_one((0).to_bytes(32, 'big'),
                                                   (0x42).to_bytes(32, 'big'))
    acct = encode_account(1, 0, sr_storage, EMPTY_CODE_HASH)
    state_root, witness_state = state_trie_one(ALICE, acct)
    addr = ALICE
    expected = struct.pack('<Q', 0) + struct.pack('<Q', 1)
elif mode == 'eoa_empty_storage':
    # EOA: storage_root = EMPTY_TRIE; never in witness.storage.
    acct = encode_account(0, 1000, EMPTY_TRIE, EMPTY_CODE_HASH)
    state_root, witness_state = state_trie_one(ALICE, acct)
    witness_storage = b''
    addr = ALICE
    expected = struct.pack('<Q', 0) + struct.pack('<Q', 0)
elif mode == 'storage_root_not_in_witness':
    # Contract with populated storage_root, BUT witness.storage doesn't
    # contain the matching node.
    sr_storage, _ = storage_trie_one((0).to_bytes(32, 'big'),
                                     (0x42).to_bytes(32, 'big'))
    acct = encode_account(1, 0, sr_storage, EMPTY_CODE_HASH)
    state_root, witness_state = state_trie_one(ALICE, acct)
    # Witness.storage has an unrelated node.
    unrelated_leaf = leaf_node(bytes_to_nibbles(b'\\xee'*32), b'\\x00')
    witness_storage = build_ssz_section([unrelated_leaf])
    addr = ALICE
    expected = struct.pack('<Q', 0) + struct.pack('<Q', 0)
elif mode == 'account_absent':
    acct = encode_account(0, 0, EMPTY_TRIE, EMPTY_CODE_HASH)
    state_root, witness_state = state_trie_one(BOB, acct)
    witness_storage = b''
    addr = ALICE  # not in trie
    expected = struct.pack('<Q', 1) + struct.pack('<Q', 0)
else:
    raise SystemExit('bad mode')

with open(sys.argv[1], 'wb') as f:
    record = (
        struct.pack('<Q', len(witness_state))
        + struct.pack('<Q', len(witness_storage))
        + state_root
        + addr
        + witness_state
        + witness_storage
    )
    f.write(record)
    pad = (-len(record)) % 8
    if pad: f.write(b'\\x00' * pad)

with open(sys.argv[2], 'wb') as f:
    f.write(expected)
" "$in_file" "$exp_file"

  "$ZISKEMU" -e gen-out/zisk_account_storage_walkable_at_state_root.elf \
    -i "$in_file" -o "$out_file" -n 6000000 \
    >"$REPO_ROOT/gen-out/zisk_aswr_${name}.emu.log" 2>&1 || true

  local exp_size
  exp_size="$(stat -c%s "$exp_file")"
  local actual expected
  actual="$(xxd -p -l "$exp_size" "$out_file" 2>/dev/null | tr -d '\n')"
  expected="$(xxd -p -l "$exp_size" "$exp_file" 2>/dev/null | tr -d '\n')"

  if [[ "$actual" == "$expected" ]]; then
    printf "  %-40s OK   %d bytes match\n" "$name" "$exp_size"
    return 0
  else
    printf "  %-40s FAIL\n    expected: %s\n    actual:   %s\n" \
      "$name" "$expected" "$actual"
    return 1
  fi
}

FAILED=0
run_case "walkable_present"              walkable_present || FAILED=1
run_case "eoa_empty_storage"             eoa_empty_storage || FAILED=1
run_case "storage_root_not_in_witness"   storage_root_not_in_witness || FAILED=1
run_case "account_absent"                account_absent || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: account_storage_walkable_at_state_root end-to-end"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
