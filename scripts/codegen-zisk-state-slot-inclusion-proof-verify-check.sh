#!/usr/bin/env bash
# codegen-zisk-state-slot-inclusion-proof-verify-check.sh
#
# End-to-end light-client slot inclusion proof: given a trusted
# state_root, address, slot_idx, and expected slot value,
# walks BOTH the state trie and the storage trie in one pass.
# Composes K28 + K29 with the intermediate storage_root never
# exposed.
#
# Spec-distinguishing rows:
#
#   | account in state? | slot in storage? | walked value | expected | status | is_match |
#   |-------------------|------------------|--------------|----------|--------|----------|
#   | yes               | yes              | V            | V        |   0    |    1     |
#   | yes               | yes              | V            | V'       |   0    |    0     |
#   | yes               | no               | 0 (SLOAD)    | 0        |   4    |    1     |
#   | yes               | no               | 0            | nonzero  |   4    |    0     |
#   | no                | n/a              | 0 (SLOAD)    | 0        |   1    |    1     |
#   | no                | n/a              | 0            | nonzero  |   1    |    0     |
#
# Output (16 bytes):
#   bytes  0.. 8 : status (0..6)
#   bytes  8..16 : is_match (u64; 0 or 1)
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

echo "==> emit zisk_state_slot_inclusion_proof_verify ELF"
lake exe codegen --program zisk_state_slot_inclusion_proof_verify \
  --halt linux93 \
  -o gen-out/zisk_state_slot_inclusion_proof_verify

REPO_ROOT="$(pwd)"

# run_case <name> <mode> [args...]
#
#   present_present  <addr> <slot_idx_be> <stored_val_be> <expected_val_be>
#   present_absent   <addr> <stored_idx_be> <lookup_idx_be> <stored_val_be> <expected_val_be>
#   account_absent   <lookup_addr> <stored_addr> <slot_idx_be> <expected_val_be>
run_case() {
  local name="$1"; shift
  local mode="$1"; shift

  local in_file="$REPO_ROOT/gen-out/zisk_sssip_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_sssip_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_sssip_${name}.expected"

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
    v = value_be.lstrip(b'\\x00')
    leaf = leaf_node(path, rlp.encode(v))
    return k256(leaf), build_ssz_section([leaf])

def state_trie_one_account(addr, account_rlp):
    path = bytes_to_nibbles(k256(addr))
    leaf = leaf_node(path, account_rlp)
    return k256(leaf), build_ssz_section([leaf])

argv = sys.argv[1:]
mode = '$mode'
parts = [
$(for arg in "$@"; do printf '  %s,\n' "\"$arg\""; done)
]

if mode == 'present_present':
    addr = bytes.fromhex(parts[0])
    slot_idx_be = bytes.fromhex(parts[1])
    stored_val_be = bytes.fromhex(parts[2])
    expected_be = bytes.fromhex(parts[3])
    # Build storage trie with one slot, get storage_root.
    storage_root, witness_storage = storage_trie_one_slot(slot_idx_be, stored_val_be)
    # Build account at addr with that storage_root.
    acct = encode_account(0, 0, storage_root, EMPTY_CODE_HASH)
    state_root, witness_state = state_trie_one_account(addr, acct)
    is_match = 1 if stored_val_be == expected_be else 0
    expected = struct.pack('<Q', 0) + struct.pack('<Q', is_match)
elif mode == 'present_absent':
    addr = bytes.fromhex(parts[0])
    stored_idx_be = bytes.fromhex(parts[1])
    lookup_idx_be = bytes.fromhex(parts[2])
    stored_val_be = bytes.fromhex(parts[3])
    expected_be = bytes.fromhex(parts[4])
    # Storage trie has stored_idx, but we look up lookup_idx.
    storage_root, witness_storage = storage_trie_one_slot(stored_idx_be, stored_val_be)
    acct = encode_account(0, 0, storage_root, EMPTY_CODE_HASH)
    state_root, witness_state = state_trie_one_account(addr, acct)
    slot_idx_be = lookup_idx_be
    is_match = 1 if expected_be == b'\\x00'*32 else 0
    expected = struct.pack('<Q', 4) + struct.pack('<Q', is_match)
elif mode == 'account_absent':
    lookup_addr = bytes.fromhex(parts[0])
    stored_addr = bytes.fromhex(parts[1])
    slot_idx_be = bytes.fromhex(parts[2])
    expected_be = bytes.fromhex(parts[3])
    # State trie has stored_addr, not lookup_addr. Storage section is irrelevant.
    storage_root, witness_storage = storage_trie_one_slot(slot_idx_be, b'\\x00'*32)
    acct = encode_account(0, 0, storage_root, EMPTY_CODE_HASH)
    state_root, witness_state = state_trie_one_account(stored_addr, acct)
    addr = lookup_addr
    is_match = 1 if expected_be == b'\\x00'*32 else 0
    expected = struct.pack('<Q', 1) + struct.pack('<Q', is_match)
elif mode == 'present_present_zero_slot':
    # Slot present, stored value is zero. RLP encoding of 0 is b'\\x80'
    # (empty bytes). Verify slot decode returns 0.
    addr = bytes.fromhex(parts[0])
    slot_idx_be = bytes.fromhex(parts[1])
    expected_be = bytes.fromhex(parts[2])
    storage_root, witness_storage = storage_trie_one_slot(slot_idx_be, b'\\x00'*32)
    acct = encode_account(0, 0, storage_root, EMPTY_CODE_HASH)
    state_root, witness_state = state_trie_one_account(addr, acct)
    stored_val_be = b'\\x00' * 32
    is_match = 1 if stored_val_be == expected_be else 0
    expected = struct.pack('<Q', 0) + struct.pack('<Q', is_match)
else:
    raise SystemExit('bad mode: ' + mode)

with open(argv[0], 'wb') as f:
    record = (
        struct.pack('<Q', len(witness_state))
        + struct.pack('<Q', len(witness_storage))
        + state_root
        + addr
        + slot_idx_be
        + expected_be
        + witness_state
        + witness_storage
    )
    f.write(record)
    pad = (-len(record)) % 8
    if pad: f.write(b'\\x00' * pad)

with open(argv[1], 'wb') as f:
    f.write(expected)
" "$in_file" "$exp_file"

  "$ZISKEMU" -e gen-out/zisk_state_slot_inclusion_proof_verify.elf \
    -i "$in_file" -o "$out_file" -n 5000000 \
    >"$REPO_ROOT/gen-out/zisk_sssip_${name}.emu.log" 2>&1 || true

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
ZERO32="$(hex32 0)"
SLOT0="$(hex32 0)"
SLOT1="$(hex32 1)"
VAL_42="$(hex32 0x42)"
VAL_43="$(hex32 0x43)"

FAILED=0
# 1) End-to-end match: account present with slot 0 = 0x42, expected 0x42.
run_case "e2e_match"                       present_present "$ALICE" "$SLOT0" "$VAL_42" "$VAL_42" || FAILED=1
# 2) End-to-end mismatch: walked 0x42, expected 0x43.
run_case "e2e_mismatch"                    present_present "$ALICE" "$SLOT0" "$VAL_42" "$VAL_43" || FAILED=1
# 3) Slot 0 present with stored value 0; expected 0 -> matches via decode.
run_case "e2e_slot_zero_decode"            present_present_zero_slot "$ALICE" "$SLOT0" "$ZERO32" || FAILED=1
# 4) Account present, slot absent, expected 0 -> status 4, is_match 1 (SLOAD).
run_case "slot_absent_expect_zero"         present_absent "$ALICE" "$SLOT0" "$SLOT1" "$VAL_42" "$ZERO32" || FAILED=1
# 5) Account present, slot absent, expected nonzero -> status 4, is_match 0.
run_case "slot_absent_expect_nonzero"      present_absent "$ALICE" "$SLOT0" "$SLOT1" "$VAL_42" "$VAL_42" || FAILED=1
# 6) Account absent, expected 0 -> status 1, is_match 1.
run_case "account_absent_expect_zero"      account_absent "$BOB" "$ALICE" "$SLOT0" "$ZERO32" || FAILED=1
# 7) Account absent, expected nonzero -> status 1, is_match 0.
run_case "account_absent_expect_nonzero"   account_absent "$BOB" "$ALICE" "$SLOT0" "$VAL_42" || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: state_slot_inclusion_proof_verify end-to-end"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
