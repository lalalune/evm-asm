#!/usr/bin/env bash
# codegen-zisk-state-extract-balance-for-address-check.sh
#
# Pure field extractor for u256 balance. Third extract
# sibling after #7233 (storage_root) and #7240 (code_hash).
# Returns 32 BE bytes with 0 default on miss.
#
# Output (40 bytes):
#   bytes  0.. 8 : status
#   bytes  8..40 : balance (32 B BE)
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

echo "==> emit zisk_state_extract_balance_for_address ELF"
lake exe codegen --program zisk_state_extract_balance_for_address \
  --halt linux93 \
  -o gen-out/zisk_state_extract_balance_for_address

REPO_ROOT="$(pwd)"

# run_case <name> <mode> [args...]
#   present <addr> <balance_int>
#   absent  <lookup_addr> <stored_addr>
run_case() {
  local name="$1"; shift
  local mode="$1"; shift

  local in_file="$REPO_ROOT/gen-out/zisk_sebal_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_sebal_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_sebal_${name}.expected"

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
    bal = int(parts[1])
    acct = encode_account(0, bal, EMPTY_TRIE, EMPTY_CODE_HASH)
    state_root, witness_state = state_trie_one(addr, acct)
    expected = struct.pack('<Q', 0) + bal.to_bytes(32, 'big')
elif mode == 'absent':
    lookup_addr = bytes.fromhex(parts[0])
    stored_addr = bytes.fromhex(parts[1])
    other = encode_account(7, 999, EMPTY_TRIE, EMPTY_CODE_HASH)
    state_root, witness_state = state_trie_one(stored_addr, other)
    addr = lookup_addr
    expected = struct.pack('<Q', 1) + b'\\x00' * 32
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

  "$ZISKEMU" -e gen-out/zisk_state_extract_balance_for_address.elf \
    -i "$in_file" -o "$out_file" -n 4000000 \
    >"$REPO_ROOT/gen-out/zisk_sebal_${name}.emu.log" 2>&1 || true

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
BIG="1606938044258990275541962092341162602522202993782792835301376"

FAILED=0
# 1) Small balance present (1 ETH).
run_case "present_small_balance"         present "$ALICE" 1000000000000000000 || FAILED=1
# 2) Zero balance present.
run_case "present_zero_balance"          present "$ALICE" 0 || FAILED=1
# 3) Big balance present (2^200 — exercises high u256 limbs).
run_case "present_big_balance"           present "$ALICE" "$BIG" || FAILED=1
# 4) Absent: spec default 0.
run_case "absent_returns_zero"           absent "$BOB" "$ALICE" || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: state_extract_balance_for_address end-to-end"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
