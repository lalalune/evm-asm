#!/usr/bin/env bash
# codegen-zisk-state-walk-extract-slot-value-check.sh
#
# End-to-end slot extractor: walks state + storage tries
# from a trusted state_root and returns the u256 slot value
# with 0 default on any absent.
#
# Output (40 bytes):
#   bytes  0.. 8 : status (0..6)
#   bytes  8..40 : u256 BE slot value (32 B)
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

echo "==> emit zisk_state_walk_extract_slot_value ELF"
lake exe codegen --program zisk_state_walk_extract_slot_value \
  --halt linux93 \
  -o gen-out/zisk_state_walk_extract_slot_value

REPO_ROOT="$(pwd)"

run_case() {
  local name="$1"; shift
  local mode="$1"; shift

  local in_file="$REPO_ROOT/gen-out/zisk_swes_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_swes_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_swes_${name}.expected"

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

def storage_trie_one_slot(slot_idx_be, value_be):
    path = bytes_to_nibbles(k256(slot_idx_be))
    leaf = leaf_node(path, rlp.encode(value_be.lstrip(b'\\x00')))
    return k256(leaf), build_ssz_section([leaf])

def state_trie_one(addr, acct_rlp):
    path = bytes_to_nibbles(k256(addr))
    leaf = leaf_node(path, acct_rlp)
    return k256(leaf), build_ssz_section([leaf])

argv = sys.argv[1:]
mode = '$mode'
parts = [
$(for arg in "$@"; do printf '  %s,\n' "\"$arg\""; done)
]

if mode == 'present_present':
    addr = bytes.fromhex(parts[0])
    slot_idx_be = bytes.fromhex(parts[1])
    val_be = bytes.fromhex(parts[2])
    storage_root, witness_storage = storage_trie_one_slot(slot_idx_be, val_be)
    acct = encode_account(0, 0, storage_root, EMPTY_CODE_HASH)
    state_root, witness_state = state_trie_one(addr, acct)
    expected = struct.pack('<Q', 0) + val_be
elif mode == 'present_absent':
    addr = bytes.fromhex(parts[0])
    stored_slot_be = bytes.fromhex(parts[1])
    lookup_slot_be = bytes.fromhex(parts[2])
    stored_val_be = bytes.fromhex(parts[3])
    storage_root, witness_storage = storage_trie_one_slot(stored_slot_be, stored_val_be)
    acct = encode_account(0, 0, storage_root, EMPTY_CODE_HASH)
    state_root, witness_state = state_trie_one(addr, acct)
    slot_idx_be = lookup_slot_be
    expected = struct.pack('<Q', 4) + b'\\x00' * 32
elif mode == 'account_absent':
    lookup_addr = bytes.fromhex(parts[0])
    stored_addr = bytes.fromhex(parts[1])
    slot_idx_be = bytes.fromhex(parts[2])
    storage_root, witness_storage = storage_trie_one_slot(slot_idx_be, b'\\x00'*32)
    acct = encode_account(0, 0, storage_root, EMPTY_CODE_HASH)
    state_root, witness_state = state_trie_one(stored_addr, acct)
    addr = lookup_addr
    expected = struct.pack('<Q', 1) + b'\\x00' * 32
else:
    raise SystemExit('bad mode')

with open(argv[0], 'wb') as f:
    record = (
        struct.pack('<Q', len(witness_state))
        + struct.pack('<Q', len(witness_storage))
        + state_root
        + addr
        + slot_idx_be
        + witness_state
        + witness_storage
    )
    f.write(record)
    pad = (-len(record)) % 8
    if pad: f.write(b'\\x00' * pad)

with open(argv[1], 'wb') as f:
    f.write(expected)
" "$in_file" "$exp_file"

  "$ZISKEMU" -e gen-out/zisk_state_walk_extract_slot_value.elf \
    -i "$in_file" -o "$out_file" -n 5000000 \
    >"$REPO_ROOT/gen-out/zisk_swes_${name}.emu.log" 2>&1 || true

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

hex32() { printf '%064x' "$1"; }

ALICE="$(printf 'aa%.0s' $(seq 1 20))"
BOB="$(printf 'bb%.0s' $(seq 1 20))"
SLOT0="$(hex32 0)"
SLOT1="$(hex32 1)"
VAL_42="$(hex32 0x42)"
VAL_DEADBEEF="$(hex32 0xdeadbeef)"

FAILED=0
# 1) Both present, slot value 0x42.
run_case "e2e_extract_small_value"        present_present "$ALICE" "$SLOT0" "$VAL_42" || FAILED=1
# 2) Both present, big value (exercises high u256 limbs).
run_case "e2e_extract_big_value"          present_present "$ALICE" "$SLOT1" "$VAL_DEADBEEF" || FAILED=1
# 3) Account present, slot absent -> status 4, value 0.
run_case "slot_absent_value_zero"         present_absent "$ALICE" "$SLOT0" "$SLOT1" "$VAL_42" || FAILED=1
# 4) Account absent -> status 1, value 0.
run_case "account_absent_value_zero"      account_absent "$BOB" "$ALICE" "$SLOT0" || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: state_walk_extract_slot_value end-to-end"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
