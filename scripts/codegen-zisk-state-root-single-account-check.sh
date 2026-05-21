#!/usr/bin/env bash
# codegen-zisk-state-root-single-account-check.sh -- PR-K33.
#
# Compute the state_root of a 1-leaf trie containing exactly
# one account. Cross-checks against Python's same computation.
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

echo "==> emit zisk_state_root_single_account ELF"
lake exe codegen --program zisk_state_root_single_account --halt linux93 \
  -o gen-out/zisk_state_root_single_account

REPO_ROOT="$(pwd)"

run_case() {
  local name="$1" addr_hex="$2" nonce="$3" balance="$4" storage_root_hex="$5" code_hash_hex="$6"

  local in_file="$REPO_ROOT/gen-out/zisk_state_root_single_account_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_state_root_single_account_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_state_root_single_account_${name}.expected"

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

def bytes_to_nibbles(b):
    out = []
    for byte in b:
        out.append(byte >> 4)
        out.append(byte & 0xf)
    return out

addr = bytes.fromhex('$addr_hex')
nonce = $nonce
balance = $balance
storage_root = bytes.fromhex('$storage_root_hex')
code_hash = bytes.fromhex('$code_hash_hex')

account_rlp = rlp.encode([nonce, balance, storage_root, code_hash])
path = bytes_to_nibbles(k256(addr))
hp = hp_encode(path, True)
leaf_rlp = rlp.encode([hp, account_rlp])
state_root = k256(leaf_rlp)

# Build input: addr_len + addr + nonce_be8 + balance_be32 + storage_root + code_hash
nonce_be = nonce.to_bytes(8, 'big')
balance_be = balance.to_bytes(32, 'big')

with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(addr)))
    f.write(addr)
    f.write(nonce_be)
    f.write(balance_be)
    f.write(storage_root)
    f.write(code_hash)
    total = 8 + len(addr) + 8 + 32 + 32 + 32
    pad = (-total) % 8
    if pad:
        f.write(b'\x00' * pad)

with open(sys.argv[2], 'wb') as f:
    f.write(state_root)
" "$in_file" "$exp_file"

  "$ZISKEMU" -e gen-out/zisk_state_root_single_account.elf \
    -i "$in_file" -o "$out_file" -n 500000 \
    >"$REPO_ROOT/gen-out/zisk_state_root_single_account_${name}.emu.log" 2>&1 || true

  local actual expected
  actual="$(xxd -p -l 32 "$out_file" 2>/dev/null | tr -d '\n')"
  expected="$(xxd -p -l 32 "$exp_file" 2>/dev/null | tr -d '\n')"

  if [[ "$actual" == "$expected" ]]; then
    printf "  %-26s OK   state_root=%s\n" "$name" "$expected"
    return 0
  else
    printf "  %-26s FAIL\n    expected: %s\n    actual:   %s\n" \
      "$name" "$expected" "$actual"
    return 1
  fi
}

ALICE="$(printf 'aa%.0s' $(seq 1 20))"
BOB="$(printf 'bb%.0s' $(seq 1 20))"
EMPTY_TRIE="56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421"
EMPTY_CODE="c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470"

FAILED=0
run_case "alice_empty"      "$ALICE" 0    0                                                            "$EMPTY_TRIE" "$EMPTY_CODE" || FAILED=1
run_case "alice_nonzero"    "$ALICE" 42   1000000000000000000                                          "$EMPTY_TRIE" "$EMPTY_CODE" || FAILED=1
run_case "alice_big_balance" "$ALICE" 1   115792089237316195423570985008687907853269984665640564039457584007913129639935 "$EMPTY_TRIE" "$EMPTY_CODE" || FAILED=1
run_case "bob_empty"        "$BOB"   0    0                                                            "$EMPTY_TRIE" "$EMPTY_CODE" || FAILED=1
run_case "alice_custom_hashes" "$ALICE" 7 99 "$(printf 'aa%.0s' $(seq 1 32))" "$(printf 'bb%.0s' $(seq 1 32))" || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: state_root_single_account matches Python ref for all account shapes"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
