#!/usr/bin/env bash
# codegen-zisk-validate-storage-root-in-witness-storage-check.sh
#
# Storage-side analog of validate_witness_state_contains_root.
# Given (header, address, witness.state, witness.storage),
# walks the state trie to the account, then looks up
# account.storage_root in witness.storage.
#
# Distinct status for EMPTY_TRIE_ROOT (legitimate "no storage")
# vs integrity violation (storage_root != EMPTY but absent
# from witness.storage).
#
# Output (24 bytes):
#   bytes  0.. 8 : status
#       0 found
#       1 account not in state trie
#       2 state-trie mpt parse error
#       3 account_decode failure
#       4 header parse fail
#       5 storage_root == EMPTY_TRIE_ROOT (no storage)
#       6 integrity violation (storage_root non-empty, not in witness.storage)
#   bytes  8..16 : matched offset (on status 0)
#   bytes 16..24 : matched length (on status 0)
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

echo "==> emit zisk_validate_storage_root_in_witness_storage ELF"
lake exe codegen --program zisk_validate_storage_root_in_witness_storage \
  --halt linux93 \
  -o gen-out/zisk_validate_storage_root_in_witness_storage

REPO_ROOT="$(pwd)"

# run_case <name> <mode> [args...]
#
#   match <addr> <storage_node_hex>
#     storage_root = keccak(storage_node_hex), witness.storage contains node.
#     Expect status 0 with matched offset/length.
#
#   integrity_violation <addr> <storage_node_hex>
#     storage_root set, but witness.storage is empty -> status 6.
#
#   empty_trie <addr>
#     account.storage_root = EMPTY_TRIE_ROOT -> status 5.
#
#   acct_miss <lookup_addr> <stored_addr> <storage_node_hex>
#     state trie has stored_addr; lookup misses -> status 1.
#
#   garbage_header <addr>
#     status 4.
run_case() {
  local name="$1"; shift
  local mode="$1"; shift

  local in_file="$REPO_ROOT/gen-out/zisk_vsr_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_vsr_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_vsr_${name}.expected"

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

def build_state_with_account(addr, account_rlp):
    path = bytes_to_nibbles(k256(addr))
    leaf = leaf_node(path, account_rlp)
    return k256(leaf), build_ssz_section([leaf])

def offset_length_of(section, target_hash):
    if not section:
        return None
    n = struct.unpack('<I', section[0:4])[0] // 4
    offsets = [struct.unpack('<I', section[4*i:4*i+4])[0] for i in range(n)]
    bounds = offsets + [len(section)]
    for i in range(n):
        elem = section[bounds[i]:bounds[i+1]]
        if k256(elem) == target_hash:
            return (bounds[i], bounds[i+1] - bounds[i])
    return None

if mode == 'match':
    addr = bytes.fromhex(parts[0])
    storage_node = bytes.fromhex(parts[1])
    storage_root = k256(storage_node)
    account = encode_account(0, 0, storage_root, EMPTY_CODE)
    state_root, witness_state = build_state_with_account(addr, account)
    witness_storage = build_ssz_section([storage_node])
    header = encode_header(state_root)
    ol = offset_length_of(witness_storage, storage_root)
    assert ol is not None
    expected = (
        struct.pack('<Q', 0)
        + struct.pack('<Q', ol[0])
        + struct.pack('<Q', ol[1])
    )
elif mode == 'integrity_violation':
    addr = bytes.fromhex(parts[0])
    storage_node = bytes.fromhex(parts[1])
    storage_root = k256(storage_node)
    account = encode_account(0, 0, storage_root, EMPTY_CODE)
    state_root, witness_state = build_state_with_account(addr, account)
    witness_storage = b''
    header = encode_header(state_root)
    expected = struct.pack('<Q', 6) + b'\\x00' * 16
elif mode == 'empty_trie':
    addr = bytes.fromhex(parts[0])
    account = encode_account(0, 0, EMPTY_TRIE, EMPTY_CODE)
    state_root, witness_state = build_state_with_account(addr, account)
    witness_storage = b''
    header = encode_header(state_root)
    expected = struct.pack('<Q', 5) + b'\\x00' * 16
elif mode == 'acct_miss':
    lookup_addr = bytes.fromhex(parts[0])
    stored_addr = bytes.fromhex(parts[1])
    storage_node = bytes.fromhex(parts[2])
    storage_root = k256(storage_node)
    account = encode_account(0, 0, storage_root, EMPTY_CODE)
    state_root, witness_state = build_state_with_account(stored_addr, account)
    witness_storage = build_ssz_section([storage_node])
    addr = lookup_addr
    header = encode_header(state_root)
    expected = struct.pack('<Q', 1) + b'\\x00' * 16
elif mode == 'garbage_header':
    addr = bytes.fromhex(parts[0])
    witness_state = b''
    witness_storage = b''
    header = b'\\x00'
    expected = struct.pack('<Q', 4) + b'\\x00' * 16
else:
    raise SystemExit('bad mode: ' + mode)

with open(argv[0], 'wb') as f:
    record = (
        struct.pack('<Q', len(header))
        + struct.pack('<Q', len(witness_state))
        + struct.pack('<Q', len(witness_storage))
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

  "$ZISKEMU" -e gen-out/zisk_validate_storage_root_in_witness_storage.elf \
    -i "$in_file" -o "$out_file" -n 4000000 \
    >"$REPO_ROOT/gen-out/zisk_vsr_${name}.emu.log" 2>&1 || true

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

FAILED=0
# Storage root present in witness.storage.
run_case "match_simple_node"           match "$ALICE" "c0" || FAILED=1
run_case "match_larger_node"           match "$ALICE" "deadbeef1122334455" || FAILED=1
# Storage root claimed in account, but witness.storage is empty.
run_case "integrity_violation"         integrity_violation "$ALICE" "c0" || FAILED=1
# EMPTY_TRIE_ROOT account: storage_root short-circuit.
run_case "empty_trie_no_storage"       empty_trie "$ALICE" || FAILED=1
# Account missing from state trie.
run_case "acct_miss_other_addr"        acct_miss "$BOB" "$ALICE" "c0" || FAILED=1
# Garbage header.
run_case "garbage_header"              garbage_header "$ALICE" || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: validate_storage_root_in_witness_storage end-to-end"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
