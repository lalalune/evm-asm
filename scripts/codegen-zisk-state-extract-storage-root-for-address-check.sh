#!/usr/bin/env bash
# codegen-zisk-state-extract-storage-root-for-address-check.sh
#
# Pure field extractor: walk state trie, return account's
# storage_root (with EMPTY_TRIE_ROOT spec default on miss).
#
# Output (40 bytes):
#   bytes  0.. 8 : status (0=present, 1=absent-default, 2/3=parse fail)
#   bytes  8..40 : storage_root (32 B)
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

echo "==> emit zisk_state_extract_storage_root_for_address ELF"
lake exe codegen --program zisk_state_extract_storage_root_for_address \
  --halt linux93 \
  -o gen-out/zisk_state_extract_storage_root_for_address

REPO_ROOT="$(pwd)"

# run_case <name> <mode> [args...]
#   present <addr> <sr_mode>   sr_mode: empty | populated:<slot_be>:<val_be>
#   absent  <lookup_addr> <stored_addr>
run_case() {
  local name="$1"; shift
  local mode="$1"; shift

  local in_file="$REPO_ROOT/gen-out/zisk_sesr_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_sesr_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_sesr_${name}.expected"

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
    raise SystemExit('bad sr_mode')

argv = sys.argv[1:]
mode = '$mode'
parts = [
$(for arg in "$@"; do printf '  %s,\n' "\"$arg\""; done)
]

def state_trie_one(addr, acct_rlp):
    path = bytes_to_nibbles(k256(addr))
    leaf = leaf_node(path, acct_rlp)
    return k256(leaf), build_ssz_section([leaf])

if mode == 'present':
    addr = bytes.fromhex(parts[0])
    sr = resolve_storage_root(parts[1])
    acct = encode_account(0, 0, sr, EMPTY_CODE_HASH)
    state_root, witness_state = state_trie_one(addr, acct)
    expected = struct.pack('<Q', 0) + sr
elif mode == 'absent':
    lookup_addr = bytes.fromhex(parts[0])
    stored_addr = bytes.fromhex(parts[1])
    other = encode_account(3, 4567, EMPTY_TRIE, EMPTY_CODE_HASH)
    state_root, witness_state = state_trie_one(stored_addr, other)
    addr = lookup_addr
    expected = struct.pack('<Q', 1) + EMPTY_TRIE
else:
    raise SystemExit('bad mode')

with open(argv[0], 'wb') as f:
    record = (
        struct.pack('<Q', len(witness_state))
        + state_root
        + addr
        + witness_state
    )
    f.write(record)
    pad = (-len(record)) % 8
    if pad: f.write(b'\\x00' * pad)

with open(argv[1], 'wb') as f:
    f.write(expected)
" "$in_file" "$exp_file"

  "$ZISKEMU" -e gen-out/zisk_state_extract_storage_root_for_address.elf \
    -i "$in_file" -o "$out_file" -n 4000000 \
    >"$REPO_ROOT/gen-out/zisk_sesr_${name}.emu.log" 2>&1 || true

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
VAL_42="$(printf '%064x' 0x42)"

FAILED=0
# 1) Account present with EMPTY_TRIE storage_root (EOA with no storage).
run_case "present_eoa_empty_root"        present "$ALICE" empty || FAILED=1
# 2) Account present with populated storage_root.
run_case "present_contract_populated"    present "$ALICE" "populated:${SLOT0}:${VAL_42}" || FAILED=1
# 3) Address absent: spec default EMPTY_TRIE_ROOT returned.
run_case "absent_returns_empty_trie"     absent "$BOB" "$ALICE" || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: state_extract_storage_root_for_address end-to-end"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
