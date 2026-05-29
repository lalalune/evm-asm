#!/usr/bin/env bash
# codegen-zisk-state-storage-root-inclusion-proof-verify-check.sh
#
# Light-client storage-root inclusion proof against a trusted
# state_root. Sibling of state_code_hash_inclusion_proof_verify
# (#7197) -- same template, different field offset (+40 vs +72)
# and different absent default (EMPTY_TRIE_ROOT vs
# EMPTY_CODE_HASH).
#
# Spec-distinguishing rows:
#
#   | account contents               | expected            | status | is_match |
#   |--------------------------------|---------------------|--------|----------|
#   | EOA (storage_root = EMPTY_TRIE)| EMPTY_TRIE_ROOT     |   0    |    1     |
#   | EOA                            | populated_root      |   0    |    0     |
#   | Contract w/ populated_root     | populated_root      |   0    |    1     |
#   | Contract w/ populated_root     | other_root          |   0    |    0     |
#   | Contract                       | EMPTY_TRIE_ROOT     |   0    |    0     |
#   | absent (default EMPTY_TRIE)    | EMPTY_TRIE_ROOT     |   1    |    1     |
#   | absent                         | any non-empty root  |   1    |    0     |
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

echo "==> emit zisk_state_storage_root_inclusion_proof_verify ELF"
lake exe codegen --program zisk_state_storage_root_inclusion_proof_verify \
  --halt linux93 \
  -o gen-out/zisk_state_storage_root_inclusion_proof_verify

REPO_ROOT="$(pwd)"

# run_case <name> <mode> [args...]
#
#   present_match    <addr> <stored_sr_mode> <expected_sr_mode>
#   present_mismatch <addr> <stored_sr_mode> <expected_sr_mode>
#   absent           <lookup_addr> <stored_addr> <expected_sr_mode>
#
#   sr_mode: empty | populated:<slot_idx_hex32_BE>:<slot_value_hex32_BE>
run_case() {
  local name="$1"; shift
  local mode="$1"; shift

  local in_file="$REPO_ROOT/gen-out/zisk_ssrip_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_ssrip_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_ssrip_${name}.expected"

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

def resolve_storage_root(mode):
    if mode == 'empty':
        return EMPTY_TRIE
    if mode.startswith('populated:'):
        _, slot_hex, val_hex = mode.split(':', 2)
        slot_be = bytes.fromhex(slot_hex)
        val_be = bytes.fromhex(val_hex)
        path = bytes_to_nibbles(k256(slot_be))
        leaf = leaf_node(path, rlp.encode(val_be.lstrip(b'\\x00')))
        return k256(leaf)
    raise SystemExit('bad sr_mode: ' + mode)

argv = sys.argv[1:]
mode = '$mode'
parts = [
$(for arg in "$@"; do printf '  %s,\n' "\"$arg\""; done)
]

def state_trie_one_account(addr, account_rlp):
    path = bytes_to_nibbles(k256(addr))
    leaf = leaf_node(path, account_rlp)
    return k256(leaf), build_ssz_section([leaf])

if mode == 'present_match' or mode == 'present_mismatch':
    addr = bytes.fromhex(parts[0])
    stored_sr = resolve_storage_root(parts[1])
    expected_sr = resolve_storage_root(parts[2])
    acct = encode_account(0, 0, stored_sr, EMPTY_CODE_HASH)
    state_root, witness_state = state_trie_one_account(addr, acct)
    is_match = 1 if stored_sr == expected_sr else 0
    if mode == 'present_match':
        assert is_match == 1, 'present_match called with mismatching roots'
    else:
        assert is_match == 0, 'present_mismatch called with matching roots'
    expected = struct.pack('<Q', 0) + struct.pack('<Q', is_match)
elif mode == 'absent':
    lookup_addr = bytes.fromhex(parts[0])
    stored_addr = bytes.fromhex(parts[1])
    expected_sr = resolve_storage_root(parts[2])
    other_acct = encode_account(0, 0, EMPTY_TRIE, EMPTY_CODE_HASH)
    state_root, witness_state = state_trie_one_account(stored_addr, other_acct)
    addr = lookup_addr
    is_match = 1 if expected_sr == EMPTY_TRIE else 0
    expected = struct.pack('<Q', 1) + struct.pack('<Q', is_match)
else:
    raise SystemExit('bad mode: ' + mode)

with open(argv[0], 'wb') as f:
    record = (
        struct.pack('<Q', len(witness_state))
        + state_root
        + addr
        + expected_sr
        + witness_state
    )
    f.write(record)
    pad = (-len(record)) % 8
    if pad: f.write(b'\\x00' * pad)

with open(argv[1], 'wb') as f:
    f.write(expected)
" "$in_file" "$exp_file"

  "$ZISKEMU" -e gen-out/zisk_state_storage_root_inclusion_proof_verify.elf \
    -i "$in_file" -o "$out_file" -n 4000000 \
    >"$REPO_ROOT/gen-out/zisk_ssrip_${name}.emu.log" 2>&1 || true

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

ALICE="$(printf 'aa%.0s' $(seq 1 20))"
BOB="$(printf 'bb%.0s' $(seq 1 20))"
SLOT0="$(printf '00%.0s' $(seq 1 32))"
SLOT1="$(printf 0000000000000000000000000000000000000000000000000000000000000001)"
VAL_42="$(printf '%064x' 0x42)"
VAL_99="$(printf '%064x' 0x99)"

POP_A="populated:${SLOT0}:${VAL_42}"
POP_B="populated:${SLOT1}:${VAL_99}"

FAILED=0
# 1) EOA present, expected EMPTY_TRIE_ROOT.
run_case "eoa_present_match_empty"         present_match "$ALICE" empty empty || FAILED=1
# 2) EOA present, expected populated -> mismatch.
run_case "eoa_present_vs_populated"        present_mismatch "$ALICE" empty "$POP_A" || FAILED=1
# 3) Contract present, expected matches its actual root.
run_case "contract_match_pop_a"            present_match "$ALICE" "$POP_A" "$POP_A" || FAILED=1
# 4) Contract present, expected a different populated root -> mismatch.
run_case "contract_pop_a_vs_pop_b"         present_mismatch "$ALICE" "$POP_A" "$POP_B" || FAILED=1
# 5) Contract with populated root, expected EMPTY_TRIE_ROOT -> mismatch
#    (distinguishes "has storage" from "empty storage").
run_case "contract_pop_vs_empty"           present_mismatch "$ALICE" "$POP_A" empty || FAILED=1
# 6) Absent, expected EMPTY_TRIE_ROOT -> status 1, is_match 1 (spec default).
run_case "absent_expect_empty"             absent "$BOB" "$ALICE" empty || FAILED=1
# 7) Absent, expected populated -> status 1, is_match 0.
run_case "absent_expect_populated"         absent "$BOB" "$ALICE" "$POP_A" || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: state_storage_root_inclusion_proof_verify end-to-end"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
