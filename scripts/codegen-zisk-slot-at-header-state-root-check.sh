#!/usr/bin/env bash
# codegen-zisk-slot-at-header-state-root-check.sh
#
# Fourth storage-proof step: from a parent header RLP, descend
# the state trie down to an account and then descend that
# account's storage trie down to a specific u256 slot value.
#
# Composes header_extract_state_root (K201) + account_at_address
# (K28) + slot_at_index (K29).
#
# Output: 8 B status, 32 B slot u256 (big-endian). Status codes:
#   0  found + decoded
#   1  account not in state trie
#   2  state-trie mpt parse error
#   3  account_decode failure
#   4  header parse / state_root size fail
#   5  slot not in storage trie
#   6  storage-trie mpt parse error
#   7  slot RLP decode failure
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

echo "==> emit zisk_slot_at_header_state_root ELF"
lake exe codegen --program zisk_slot_at_header_state_root \
  --halt linux93 \
  -o gen-out/zisk_slot_at_header_state_root

REPO_ROOT="$(pwd)"

# run_case <name> <mode> [args...]
#   match <addr> <slot_idx_hex_32> <slot_value_dec> <nonce> <balance>
#       Single-leaf storage trie holding slot_idx -> slot_value;
#       single-leaf state trie holding addr -> account whose
#       storage_root is that storage trie's root.
#       header.state_root = root of the state trie.
#   slot_miss <addr> <lookup_slot_idx_hex> <stored_slot_idx_hex> <slot_value_dec> <nonce> <balance>
#       state trie has the account; storage trie is keyed on
#       stored_slot_idx; lookup uses lookup_slot_idx (different).
#       Expected status 5.
#   acct_miss <lookup_addr> <stored_addr> <slot_idx_hex> <slot_value_dec> <nonce> <balance>
#       state trie keyed on stored_addr; lookup uses lookup_addr.
#       Expected status 1.
#   garbage_header <addr> <slot_idx_hex>
#       1-byte invalid header. Expected status 4.
run_case() {
  local name="$1"; shift
  local mode="$1"; shift

  local in_file="$REPO_ROOT/gen-out/zisk_sahsr_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_sahsr_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_sahsr_${name}.expected"

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
        out.append(byte >> 4)
        out.append(byte & 0xf)
    return out

def build_ssz_section(elements):
    n = len(elements)
    if n == 0:
        return b''
    section = b''
    offset = 4 * n
    for e in elements:
        section += struct.pack('<I', offset)
        offset += len(e)
    for e in elements:
        section += e
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

EMPTY_CODE = bytes.fromhex('c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470')

argv = sys.argv[1:]
mode = '$mode'
parts = [
$(for arg in "$@"; do printf '  %s,\n' "\"$arg\""; done)
]

def build_storage_trie(slot_idx, slot_value):
    # Storage trie leaf: keccak(slot_idx) -> rlp(slot_value).
    path = bytes_to_nibbles(k256(slot_idx))
    encoded = rlp.encode(slot_value)
    leaf = leaf_node(path, encoded)
    return k256(leaf), build_ssz_section([leaf])

def build_state_trie(addr, account_rlp):
    path = bytes_to_nibbles(k256(addr))
    leaf = leaf_node(path, account_rlp)
    return k256(leaf), build_ssz_section([leaf])

if mode == 'match':
    addr = bytes.fromhex(parts[0])
    slot_idx = bytes.fromhex(parts[1])
    slot_value = int(parts[2])
    nonce = int(parts[3])
    balance = int(parts[4])
    storage_root, witness_storage = build_storage_trie(slot_idx, slot_value)
    account = encode_account(nonce, balance, storage_root, EMPTY_CODE)
    state_root, witness_state = build_state_trie(addr, account)
    header = encode_header(state_root)
    expected = struct.pack('<Q', 0) + slot_value.to_bytes(32, 'big')
elif mode == 'slot_miss':
    addr = bytes.fromhex(parts[0])
    lookup_slot = bytes.fromhex(parts[1])
    stored_slot = bytes.fromhex(parts[2])
    slot_value = int(parts[3])
    nonce = int(parts[4])
    balance = int(parts[5])
    storage_root, witness_storage = build_storage_trie(stored_slot, slot_value)
    account = encode_account(nonce, balance, storage_root, EMPTY_CODE)
    state_root, witness_state = build_state_trie(addr, account)
    header = encode_header(state_root)
    slot_idx = lookup_slot
    expected = struct.pack('<Q', 5) + b'\\x00' * 32
elif mode == 'acct_miss':
    lookup_addr = bytes.fromhex(parts[0])
    stored_addr = bytes.fromhex(parts[1])
    slot_idx = bytes.fromhex(parts[2])
    slot_value = int(parts[3])
    nonce = int(parts[4])
    balance = int(parts[5])
    storage_root, witness_storage = build_storage_trie(slot_idx, slot_value)
    account = encode_account(nonce, balance, storage_root, EMPTY_CODE)
    state_root, witness_state = build_state_trie(stored_addr, account)
    header = encode_header(state_root)
    addr = lookup_addr
    expected = struct.pack('<Q', 1) + b'\\x00' * 32
elif mode == 'garbage_header':
    addr = bytes.fromhex(parts[0])
    slot_idx = bytes.fromhex(parts[1])
    witness_state = b''
    witness_storage = b''
    header = b'\\x00'
    expected = struct.pack('<Q', 4) + b'\\x00' * 32
else:
    raise SystemExit('bad mode: ' + mode)

with open(argv[0], 'wb') as f:
    record = (
        struct.pack('<Q', len(header))
        + struct.pack('<Q', len(witness_state))
        + struct.pack('<Q', len(witness_storage))
        + slot_idx
        + addr
        + header
        + witness_state
        + witness_storage
    )
    f.write(record)
    pad = (-len(record)) % 8
    if pad: f.write(b'\\x00' * pad)

with open(argv[1], 'wb') as f:
    f.write(expected)
" "$in_file" "$exp_file"

  "$ZISKEMU" -e gen-out/zisk_slot_at_header_state_root.elf \
    -i "$in_file" -o "$out_file" -n 8000000 \
    >"$REPO_ROOT/gen-out/zisk_sahsr_${name}.emu.log" 2>&1 || true

  local exp_size; exp_size="$(stat -c%s "$exp_file")"
  local actual expected
  actual="$(xxd -p -l "$exp_size" "$out_file" 2>/dev/null | tr -d '\n')"
  expected="$(xxd -p -l "$exp_size" "$exp_file" 2>/dev/null | tr -d '\n')"

  if [[ "$actual" == "$expected" ]]; then
    printf "  %-30s OK   %d bytes match\n" "$name" "$exp_size"
    return 0
  else
    printf "  %-30s FAIL\n    expected: %s\n    actual:   %s\n" \
      "$name" "$expected" "$actual"
    return 1
  fi
}

ALICE="$(printf 'aa%.0s' $(seq 1 20))"
BOB="$(printf 'bb%.0s' $(seq 1 20))"
SLOT0="0000000000000000000000000000000000000000000000000000000000000000"
SLOT1="0000000000000000000000000000000000000000000000000000000000000001"
SLOT2="0000000000000000000000000000000000000000000000000000000000000002"

FAILED=0
run_case "match_slot0_zero"        match "$ALICE" "$SLOT0" 0 0 0 || FAILED=1
run_case "match_slot0_small"       match "$ALICE" "$SLOT0" 42 0 0 || FAILED=1
run_case "match_slot1_huge"        match "$ALICE" "$SLOT1" 115792089237316195423570985008687907853269984665640564039457584007913129639935 7 99 || FAILED=1
run_case "slot_miss_other_index"   slot_miss "$ALICE" "$SLOT2" "$SLOT1" 100 0 0 || FAILED=1
run_case "acct_miss_other_addr"    acct_miss "$BOB" "$ALICE" "$SLOT0" 7 0 0 || FAILED=1
run_case "garbage_header"          garbage_header "$ALICE" "$SLOT0" || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: slot_at_header_state_root end-to-end"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
