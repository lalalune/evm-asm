#!/usr/bin/env bash
# codegen-zisk-account-at-header-state-root-check.sh
#
# Third storage-proof step: given (parent_header_rlp, address,
# witness.state list), extract the header's state_root and walk
# the state trie down to the account leaf in one shot.
#
# Composes header_extract_state_root (K201) + account_at_address
# (K28). Returns:
#   0  found + decoded
#   1  not found in trie
#   2  mpt_walk parse error
#   3  account_decode failure
#   4  header parse / state_root size fail
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

echo "==> emit zisk_account_at_header_state_root ELF"
lake exe codegen --program zisk_account_at_header_state_root \
  --halt linux93 \
  -o gen-out/zisk_account_at_header_state_root

REPO_ROOT="$(pwd)"

# run_case <name> <mode> ...
#   match <addr_hex> <nonce> <balance> <storage_root_hex> <code_hash_hex>
#     Single-leaf trie keyed on addr; header.state_root = root of that trie.
#   miss <lookup_addr_hex> <trie_addr_hex> <nonce> <balance> <storage_root_hex> <code_hash_hex>
#     Single-leaf trie keyed on trie_addr; look up lookup_addr (different).
#   garbage_header <lookup_addr_hex>
#     1-byte invalid header (state_root field unreachable).
#   wrong_state_root <addr_hex> <nonce> <balance> <storage_root_hex> <code_hash_hex>
#     header.state_root set to zeros; the witness contains the correct leaf.
#     Should be MPT parse error (root_hash points at a non-existent node).
run_case() {
  local name="$1"; shift
  local mode="$1"; shift

  local in_file="$REPO_ROOT/gen-out/zisk_aahsr_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_aahsr_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_aahsr_${name}.expected"

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

argv = sys.argv[1:]
mode = '$mode'
parts = [
$(for arg in "$@"; do printf '  %s,\n' "\"$arg\""; done)
]

if mode == 'match':
    addr = bytes.fromhex(parts[0])
    nonce = int(parts[1])
    balance = int(parts[2])
    storage_root = bytes.fromhex(parts[3])
    code_hash = bytes.fromhex(parts[4])
    account = encode_account(nonce, balance, storage_root, code_hash)
    path = bytes_to_nibbles(k256(addr))
    leaf = leaf_node(path, account)
    root = k256(leaf)
    witness = build_ssz_section([leaf])
    header = encode_header(root)
    lookup_addr = addr
    expected = struct.pack('<Q', 0)   # status
    expected += struct.pack('<Q', nonce)
    expected += balance.to_bytes(32, 'big')
    expected += storage_root
    expected += code_hash
elif mode == 'miss':
    lookup_addr = bytes.fromhex(parts[0])
    trie_addr = bytes.fromhex(parts[1])
    nonce = int(parts[2])
    balance = int(parts[3])
    storage_root = bytes.fromhex(parts[4])
    code_hash = bytes.fromhex(parts[5])
    account = encode_account(nonce, balance, storage_root, code_hash)
    path = bytes_to_nibbles(k256(trie_addr))
    leaf = leaf_node(path, account)
    root = k256(leaf)
    witness = build_ssz_section([leaf])
    header = encode_header(root)
    expected = struct.pack('<Q', 1) + b'\\x00' * 104
elif mode == 'garbage_header':
    lookup_addr = bytes.fromhex(parts[0])
    witness = b''
    header = b'\\x00'
    expected = struct.pack('<Q', 4) + b'\\x00' * 104
elif mode == 'wrong_state_root':
    addr = bytes.fromhex(parts[0])
    nonce = int(parts[1])
    balance = int(parts[2])
    storage_root = bytes.fromhex(parts[3])
    code_hash = bytes.fromhex(parts[4])
    account = encode_account(nonce, balance, storage_root, code_hash)
    path = bytes_to_nibbles(k256(addr))
    leaf = leaf_node(path, account)
    witness = build_ssz_section([leaf])
    header = encode_header(b'\\x00' * 32)
    lookup_addr = addr
    # state_root = zeros: witness_lookup_by_hash misses on the
    # root node and mpt_walk surfaces this as not-found (1).
    expected = struct.pack('<Q', 1) + b'\\x00' * 104
else:
    raise SystemExit('bad mode: ' + mode)

with open(argv[0], 'wb') as f:
    record = (
        struct.pack('<Q', len(header))
        + struct.pack('<Q', len(witness))
        + struct.pack('<Q', len(lookup_addr))
        + header + lookup_addr + witness
    )
    f.write(record)
    pad = (-len(record)) % 8
    if pad: f.write(b'\\x00' * pad)

with open(argv[1], 'wb') as f:
    f.write(expected)
" "$in_file" "$exp_file"

  "$ZISKEMU" -e gen-out/zisk_account_at_header_state_root.elf \
    -i "$in_file" -o "$out_file" -n 4000000 \
    >"$REPO_ROOT/gen-out/zisk_aahsr_${name}.emu.log" 2>&1 || true

  local exp_size; exp_size="$(stat -c%s "$exp_file")"
  local actual expected
  actual="$(xxd -p -l "$exp_size" "$out_file" 2>/dev/null | tr -d '\n')"
  expected="$(xxd -p -l "$exp_size" "$exp_file" 2>/dev/null | tr -d '\n')"

  if [[ "$actual" == "$expected" ]]; then
    printf "  %-26s OK   %d bytes match\n" "$name" "$exp_size"
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
run_case "alice_match_zero"     match "$ALICE" 0 0 "$EMPTY_TRIE" "$EMPTY_CODE" || FAILED=1
run_case "alice_match_nonzero"  match "$ALICE" 42 1000000000000000000 "$EMPTY_TRIE" "$EMPTY_CODE" || FAILED=1
run_case "alice_match_huge"     match "$ALICE" 1 115792089237316195423570985008687907853269984665640564039457584007913129639935 "$EMPTY_TRIE" "$EMPTY_CODE" || FAILED=1
run_case "bob_miss"             miss "$BOB" "$ALICE" 7 99 "$EMPTY_TRIE" "$EMPTY_CODE" || FAILED=1
run_case "garbage_header"       garbage_header "$ALICE" || FAILED=1
run_case "wrong_state_root"     wrong_state_root "$ALICE" 0 0 "$EMPTY_TRIE" "$EMPTY_CODE" || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: account_at_header_state_root end-to-end"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
