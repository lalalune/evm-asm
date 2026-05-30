#!/usr/bin/env bash
# codegen-zisk-witness-headers-account-at-index-address-check.sh
#
# Historical-state account lookup: walk the state trie under
# witness.headers[i].state_root for a given address. Returns
# the 104-byte account struct.
#
# Output (112 bytes):
#   bytes  0.. 8 : status (0..6)
#   bytes  8..16 : nonce (u64)
#   bytes 16..48 : balance (32 BE)
#   bytes 48..80 : storage_root (32)
#   bytes 80..112: code_hash (32)
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

echo "==> emit zisk_witness_headers_account_at_index_address ELF"
lake exe codegen --program zisk_witness_headers_account_at_index_address \
  --halt linux93 \
  -o gen-out/zisk_witness_headers_account_at_index_address

REPO_ROOT="$(pwd)"

run_case() {
  local name="$1"; shift
  local mode="$1"; shift
  local header_idx="$1"; shift

  local in_file="$REPO_ROOT/gen-out/zisk_whai_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_whai_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_whai_${name}.expected"

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

def encode_header(state_root):
    fields = [
        b'\\x11'*32, b'\\x22'*32, b'\\x33'*20, state_root, b'\\x55'*32,
        b'\\x66'*32, b'\\x00'*256, b'', b'\\x01', b'\\x83\\xff\\xff\\xff',
        b'', b'\\x83\\x01\\x02\\x03', b'', b'\\x77'*32, b'\\x00'*8,
    ]
    return rlp.encode(fields)

EMPTY_TRIE = bytes.fromhex('56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421')
EMPTY_CODE_HASH = bytes.fromhex('c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470')

def state_trie_one(addr, acct_rlp):
    path = bytes_to_nibbles(k256(addr))
    leaf = leaf_node(path, acct_rlp)
    return k256(leaf), build_ssz_section([leaf])

def pack_struct(status, nonce, balance_int, sr, ch):
    return (
        struct.pack('<Q', status)
        + struct.pack('<Q', nonce)
        + balance_int.to_bytes(32, 'big')
        + sr
        + ch
    )

argv = sys.argv[1:]
mode = '$mode'
header_idx = int('$header_idx')

ALICE = b'\\xaa' * 20
BOB = b'\\xbb' * 20

if mode == 'present_idx0':
    nonce, balance = 5, 1000
    acct = encode_account(nonce, balance, EMPTY_TRIE, EMPTY_CODE_HASH)
    state_root_0, witness_state = state_trie_one(ALICE, acct)
    headers = [encode_header(state_root_0), encode_header(b'\\x66'*32)]
    witness_headers = build_ssz_section(headers)
    addr = ALICE
    expected = pack_struct(0, nonce, balance, EMPTY_TRIE, EMPTY_CODE_HASH)
elif mode == 'present_idx1':
    nonce, balance = 7, 5555
    acct = encode_account(nonce, balance, EMPTY_TRIE, EMPTY_CODE_HASH)
    state_root_1, witness_state = state_trie_one(ALICE, acct)
    headers = [encode_header(b'\\x66'*32), encode_header(state_root_1)]
    witness_headers = build_ssz_section(headers)
    addr = ALICE
    expected = pack_struct(0, nonce, balance, EMPTY_TRIE, EMPTY_CODE_HASH)
elif mode == 'absent_account':
    other = encode_account(3, 4567, EMPTY_TRIE, EMPTY_CODE_HASH)
    state_root_0, witness_state = state_trie_one(BOB, other)
    headers = [encode_header(state_root_0)]
    witness_headers = build_ssz_section(headers)
    addr = ALICE
    expected = pack_struct(4, 0, 0, b'\\x00'*32, b'\\x00'*32)
elif mode == 'oob_idx':
    other = encode_account(3, 4567, EMPTY_TRIE, EMPTY_CODE_HASH)
    state_root_0, witness_state = state_trie_one(BOB, other)
    headers = [encode_header(state_root_0)]
    witness_headers = build_ssz_section(headers)
    addr = ALICE
    expected = pack_struct(1, 0, 0, b'\\x00'*32, b'\\x00'*32)
elif mode == 'header_garbage':
    other = encode_account(3, 4567, EMPTY_TRIE, EMPTY_CODE_HASH)
    state_root_0, witness_state = state_trie_one(BOB, other)
    # 2nd header is too small to RLP-decode.
    witness_headers = build_ssz_section([encode_header(state_root_0), b'\\x00'])
    addr = ALICE
    expected = pack_struct(2, 0, 0, b'\\x00'*32, b'\\x00'*32)
else:
    raise SystemExit('bad mode')

with open(argv[0], 'wb') as f:
    record = (
        struct.pack('<Q', len(witness_headers))
        + struct.pack('<Q', len(witness_state))
        + struct.pack('<Q', header_idx)
        + addr
        + witness_headers
        + witness_state
    )
    f.write(record)
    pad = (-len(record)) % 8
    if pad: f.write(b'\\x00' * pad)

with open(argv[1], 'wb') as f:
    f.write(expected)
" "$in_file" "$exp_file"

  "$ZISKEMU" -e gen-out/zisk_witness_headers_account_at_index_address.elf \
    -i "$in_file" -o "$out_file" -n 5000000 \
    >"$REPO_ROOT/gen-out/zisk_whai_${name}.emu.log" 2>&1 || true

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

FAILED=0
# 1) Walk header 0's state for an existing account.
run_case "present_at_header0"           present_idx0 0 || FAILED=1
# 2) Walk header 1's state -- different state_root, different balance.
run_case "present_at_header1"           present_idx1 1 || FAILED=1
# 3) Header 0 state for absent account -> status 4.
run_case "absent_account_at_header0"    absent_account 0 || FAILED=1
# 4) Header_idx out of bounds -> status 1.
run_case "header_idx_oob"               oob_idx 99 || FAILED=1
# 5) Header at index garbage -> status 2.
run_case "header_garbage_at_idx1"       header_garbage 1 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: witness_headers_account_at_index_address end-to-end"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
