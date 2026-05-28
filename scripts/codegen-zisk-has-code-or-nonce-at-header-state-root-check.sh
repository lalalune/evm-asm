#!/usr/bin/env bash
# codegen-zisk-has-code-or-nonce-at-header-state-root-check.sh
#
# EIP-684 CREATE collision predicate over a stateless witness.
# Given (header, address, witness.state) returns 1 iff the
# account has nonce > 0 OR code_hash != EMPTY_CODE_HASH.
#
# Notable distinction from EIP-1052 (EXTCODEHASH): this predicate
# does NOT factor in the balance field. A pure-EOA with only
# non-zero balance is NOT a CREATE collision target.
#
# Output (16 bytes):
#   bytes  0.. 8 : status
#       0 success
#       2 state-trie mpt parse
#       3 account_decode failure
#       4 header parse fail
#   bytes  8..16 : predicate (u64; 0 or 1)
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

echo "==> emit zisk_has_code_or_nonce_at_header_state_root ELF"
lake exe codegen --program zisk_has_code_or_nonce_at_header_state_root \
  --halt linux93 \
  -o gen-out/zisk_has_code_or_nonce_at_header_state_root

REPO_ROOT="$(pwd)"

# run_case <name> <mode> [args...]
#
#   account <addr> <nonce> <balance> <code_mode>
#     code_mode is one of:
#       empty   - code_hash = EMPTY_CODE_HASH
#       contract:<hex> - code_hash = keccak(hex)
#
#   missing <lookup_addr> <stored_addr> <nonce> <balance>
#     state trie has stored_addr; lookup misses; expect predicate 0.
#
#   garbage_header <addr>
#     1-byte invalid header; status 4.
run_case() {
  local name="$1"; shift
  local mode="$1"; shift

  local in_file="$REPO_ROOT/gen-out/zisk_hcon_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_hcon_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_hcon_${name}.expected"

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
EMPTY_CODE_HASH = bytes.fromhex('c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470')

argv = sys.argv[1:]
mode = '$mode'
parts = [
$(for arg in "$@"; do printf '  %s,\n' "\"$arg\""; done)
]

def build_state_with_account(addr, account_rlp):
    path = bytes_to_nibbles(k256(addr))
    leaf = leaf_node(path, account_rlp)
    return k256(leaf), build_ssz_section([leaf])

def resolve_code_hash(code_mode):
    if code_mode == 'empty':
        return EMPTY_CODE_HASH
    if code_mode.startswith('contract:'):
        return k256(bytes.fromhex(code_mode.split(':', 1)[1]))
    raise SystemExit('bad code_mode: ' + code_mode)

if mode == 'account':
    addr = bytes.fromhex(parts[0])
    nonce = int(parts[1])
    balance = int(parts[2])
    code_hash = resolve_code_hash(parts[3])
    account = encode_account(nonce, balance, EMPTY_TRIE, code_hash)
    state_root, witness_state = build_state_with_account(addr, account)
    header = encode_header(state_root)
    pred = 1 if (nonce > 0 or code_hash != EMPTY_CODE_HASH) else 0
    expected = struct.pack('<Q', 0) + struct.pack('<Q', pred)
elif mode == 'missing':
    lookup_addr = bytes.fromhex(parts[0])
    stored_addr = bytes.fromhex(parts[1])
    nonce = int(parts[2])
    balance = int(parts[3])
    account = encode_account(nonce, balance, EMPTY_TRIE, EMPTY_CODE_HASH)
    state_root, witness_state = build_state_with_account(stored_addr, account)
    header = encode_header(state_root)
    addr = lookup_addr
    expected = struct.pack('<Q', 0) + struct.pack('<Q', 0)
elif mode == 'garbage_header':
    addr = bytes.fromhex(parts[0])
    witness_state = b''
    header = b'\\x00'
    expected = struct.pack('<Q', 4) + struct.pack('<Q', 0)
else:
    raise SystemExit('bad mode: ' + mode)

with open(argv[0], 'wb') as f:
    record = (
        struct.pack('<Q', len(header))
        + struct.pack('<Q', len(witness_state))
        + addr
        + header
        + witness_state
    )
    f.write(record)
    pad = (-len(record)) % 8
    if pad: f.write(b'\\x00' * pad)

with open(argv[1], 'wb') as f:
    f.write(expected)
" "$in_file" "$exp_file"

  "$ZISKEMU" -e gen-out/zisk_has_code_or_nonce_at_header_state_root.elf \
    -i "$in_file" -o "$out_file" -n 4000000 \
    >"$REPO_ROOT/gen-out/zisk_hcon_${name}.emu.log" 2>&1 || true

  local exp_size; exp_size="$(stat -c%s "$exp_file")"
  local actual expected
  actual="$(xxd -p -l "$exp_size" "$out_file" 2>/dev/null | tr -d '\n')"
  expected="$(xxd -p -l "$exp_size" "$exp_file" 2>/dev/null | tr -d '\n')"

  if [[ "$actual" == "$expected" ]]; then
    printf "  %-36s OK   %d bytes match\n" "$name" "$exp_size"
    return 0
  else
    printf "  %-36s FAIL\n    expected: %s\n    actual:   %s\n" \
      "$name" "$expected" "$actual"
    return 1
  fi
}

ALICE="$(printf 'aa%.0s' $(seq 1 20))"
BOB="$(printf 'bb%.0s' $(seq 1 20))"

FAILED=0
# Contract account -> predicate 1 (code_hash != EMPTY).
run_case "contract_nonzero_state"         account "$ALICE" 7 1000 "contract:6000" || FAILED=1
# EOA with only nonce > 0 -> predicate 1.
run_case "eoa_with_nonce_only"            account "$ALICE" 1 0 "empty" || FAILED=1
# EOA with only balance > 0 -> predicate 0 (EIP-684 IGNORES balance!).
run_case "eoa_with_balance_only"          account "$ALICE" 0 1000000000000000000 "empty" || FAILED=1
# Account with non-zero nonce AND balance AND code -> predicate 1.
run_case "fully_active_contract"          account "$ALICE" 42 1000 "contract:6000" || FAILED=1
# Fully empty account present in trie -> predicate 0.
run_case "fully_empty_in_trie"            account "$ALICE" 0 0 "empty" || FAILED=1
# Account missing -> predicate 0.
run_case "missing_account"                missing "$BOB" "$ALICE" 7 1000 || FAILED=1
# Garbage header -> status 4.
run_case "garbage_header"                 garbage_header "$ALICE" || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: has_code_or_nonce_at_header_state_root (EIP-684) end-to-end"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
