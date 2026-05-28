#!/usr/bin/env bash
# codegen-zisk-sload-at-header-state-root-check.sh
#
# Witness-side EVM SLOAD opcode. Returns the u256 value an
# SLOAD(slot) frame in `addr`'s context would push:
#   * 0 if the account is absent
#   * 0 if account.storage_root == EMPTY_TRIE_ROOT
#   * 0 if the slot is not in the storage trie
#   * the decoded u256 otherwise
#
# Distinct from PR #7145 slot_at_header_state_root, which surfaces
# those "not found" cases as distinct status codes (1, 5). SLOAD
# flattens them all into (status=0, value=0) per the spec.
#
# Output (40 bytes):
#   bytes  0.. 8 : status (0 / 2 / 3 / 4 / 6 / 7)
#   bytes  8..40 : slot value (u256 BE)
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

echo "==> emit zisk_sload_at_header_state_root ELF"
lake exe codegen --program zisk_sload_at_header_state_root \
  --halt linux93 \
  -o gen-out/zisk_sload_at_header_state_root

REPO_ROOT="$(pwd)"

# run_case <name> <mode> [args...]
#
#   match <addr> <slot_idx_hex> <slot_value_dec> <nonce> <balance>
#     Account exists with single-leaf storage; slot found.
#     Expect (0, slot_value).
#
#   slot_not_in_trie <addr> <lookup_slot_hex> <stored_slot_hex> <slot_value_dec>
#     Storage trie has stored_slot; lookup uses lookup_slot.
#     Per SLOAD spec: returns 0 (NOT an error). Expect (0, 0).
#
#   empty_storage <addr>
#     Account exists with storage_root == EMPTY_TRIE_ROOT.
#     Per SLOAD spec: any SLOAD returns 0. Expect (0, 0).
#
#   missing_account <lookup_addr> <stored_addr> <slot_idx_hex>
#     Account not in state trie. SLOAD returns 0. Expect (0, 0).
#
#   garbage_header <addr> <slot_idx_hex>  -> (4, 0)
run_case() {
  local name="$1"; shift
  local mode="$1"; shift

  local in_file="$REPO_ROOT/gen-out/zisk_sload_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_sload_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_sload_${name}.expected"

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

EMPTY_TRIE = bytes.fromhex('56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421')
EMPTY_CODE = bytes.fromhex('c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470')

argv = sys.argv[1:]
mode = '$mode'
parts = [
$(for arg in "$@"; do printf '  %s,\n' "\"$arg\""; done)
]

def build_storage_trie(slot_idx, slot_value):
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
elif mode == 'slot_not_in_trie':
    addr = bytes.fromhex(parts[0])
    lookup_slot = bytes.fromhex(parts[1])
    stored_slot = bytes.fromhex(parts[2])
    slot_value = int(parts[3])
    storage_root, witness_storage = build_storage_trie(stored_slot, slot_value)
    account = encode_account(0, 0, storage_root, EMPTY_CODE)
    state_root, witness_state = build_state_trie(addr, account)
    header = encode_header(state_root)
    slot_idx = lookup_slot
    expected = struct.pack('<Q', 0) + b'\\x00' * 32
elif mode == 'empty_storage':
    addr = bytes.fromhex(parts[0])
    account = encode_account(0, 0, EMPTY_TRIE, EMPTY_CODE)
    state_root, witness_state = build_state_trie(addr, account)
    witness_storage = b''
    header = encode_header(state_root)
    slot_idx = b'\\x00' * 32
    expected = struct.pack('<Q', 0) + b'\\x00' * 32
elif mode == 'missing_account':
    lookup_addr = bytes.fromhex(parts[0])
    stored_addr = bytes.fromhex(parts[1])
    slot_idx = bytes.fromhex(parts[2])
    account = encode_account(0, 0, EMPTY_TRIE, EMPTY_CODE)
    state_root, witness_state = build_state_trie(stored_addr, account)
    witness_storage = b''
    addr = lookup_addr
    header = encode_header(state_root)
    expected = struct.pack('<Q', 0) + b'\\x00' * 32
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

  "$ZISKEMU" -e gen-out/zisk_sload_at_header_state_root.elf \
    -i "$in_file" -o "$out_file" -n 8000000 \
    >"$REPO_ROOT/gen-out/zisk_sload_${name}.emu.log" 2>&1 || true

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
run_case "match_small_value"        match "$ALICE" "$SLOT0" 42 0 0 || FAILED=1
run_case "match_huge_value"         match "$ALICE" "$SLOT1" 115792089237316195423570985008687907853269984665640564039457584007913129639935 7 99 || FAILED=1
# The three SLOAD-spec edge cases that get mapped to (0, 0):
run_case "slot_not_in_storage_trie" slot_not_in_trie "$ALICE" "$SLOT2" "$SLOT1" 42 || FAILED=1
run_case "empty_storage_trie"       empty_storage "$ALICE" || FAILED=1
run_case "missing_account"          missing_account "$BOB" "$ALICE" "$SLOT0" || FAILED=1
# Structural fail.
run_case "garbage_header"           garbage_header "$ALICE" "$SLOT0" || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: sload_at_header_state_root end-to-end"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
