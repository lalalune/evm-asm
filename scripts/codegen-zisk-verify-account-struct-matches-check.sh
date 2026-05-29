#!/usr/bin/env bash
# codegen-zisk-verify-account-struct-matches-check.sh
#
# Walk witness.state to (header.state_root, address), then bytewise
# compare the decoded 104-byte account struct against a caller-supplied
# expected struct. Returns is_match = 1 iff every field matches.
#
# Output (16 bytes):
#   bytes  0.. 8 : status
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

echo "==> emit zisk_verify_account_struct_matches ELF"
lake exe codegen --program zisk_verify_account_struct_matches \
  --halt linux93 \
  -o gen-out/zisk_verify_account_struct_matches

REPO_ROOT="$(pwd)"

# run_case <name> <mode> <addr_hex> <nonce> <balance> <stored_storage_root_hex> <stored_code_hash_hex> \
#                       [<expected_nonce> <expected_balance> <expected_storage_root_hex> <expected_code_hash_hex>]
# mode: exact (expected = stored), mismatch_<field>, missing
run_case() {
  local name="$1"; shift
  local mode="$1"; shift

  local in_file="$REPO_ROOT/gen-out/zisk_vasm_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_vasm_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_vasm_${name}.expected"

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

def encode_struct(nonce, balance, storage_root, code_hash):
    # 104-byte struct layout matching account_at_address output.
    return (
        struct.pack('<Q', nonce)
        + balance.to_bytes(32, 'big')
        + storage_root
        + code_hash
    )

def build_state_with_account(addr, nonce, balance, storage_root, code_hash):
    account = encode_account(nonce, balance, storage_root, code_hash)
    path = bytes_to_nibbles(k256(addr))
    leaf = leaf_node(path, account)
    return k256(leaf), build_ssz_section([leaf])

addr = bytes.fromhex(parts[0])
stored_nonce = int(parts[1])
stored_balance = int(parts[2])
stored_storage_root = bytes.fromhex(parts[3])
stored_code_hash = bytes.fromhex(parts[4])

if mode == 'exact':
    exp_nonce = stored_nonce
    exp_balance = stored_balance
    exp_storage_root = stored_storage_root
    exp_code_hash = stored_code_hash
    expected_is_match = 1
    expected_status = 0
elif mode == 'mismatch_nonce':
    exp_nonce = stored_nonce + 1
    exp_balance = stored_balance
    exp_storage_root = stored_storage_root
    exp_code_hash = stored_code_hash
    expected_is_match = 0
    expected_status = 0
elif mode == 'mismatch_balance':
    exp_nonce = stored_nonce
    exp_balance = stored_balance + 1
    exp_storage_root = stored_storage_root
    exp_code_hash = stored_code_hash
    expected_is_match = 0
    expected_status = 0
elif mode == 'mismatch_storage_root':
    exp_nonce = stored_nonce
    exp_balance = stored_balance
    exp_storage_root = bytes.fromhex('a' * 64)
    exp_code_hash = stored_code_hash
    expected_is_match = 0
    expected_status = 0
elif mode == 'mismatch_code_hash':
    exp_nonce = stored_nonce
    exp_balance = stored_balance
    exp_storage_root = stored_storage_root
    exp_code_hash = bytes.fromhex('b' * 64)
    expected_is_match = 0
    expected_status = 0
elif mode == 'missing':
    # Build witness with a different account; lookup the requested one.
    exp_nonce = stored_nonce
    exp_balance = stored_balance
    exp_storage_root = stored_storage_root
    exp_code_hash = stored_code_hash
    expected_is_match = 0
    expected_status = 1
else:
    raise SystemExit('bad mode: ' + mode)

if mode == 'missing':
    other_addr = b'\\xbb' * 20
    state_root, witness_state = build_state_with_account(other_addr, stored_nonce, stored_balance, stored_storage_root, stored_code_hash)
else:
    state_root, witness_state = build_state_with_account(addr, stored_nonce, stored_balance, stored_storage_root, stored_code_hash)
header = encode_header(state_root)
expected_struct = encode_struct(exp_nonce, exp_balance, exp_storage_root, exp_code_hash)

expected = struct.pack('<Q', expected_status) + struct.pack('<Q', expected_is_match)

with open(argv[0], 'wb') as f:
    record = (
        struct.pack('<Q', len(header))
        + struct.pack('<Q', len(witness_state))
        + addr
        + expected_struct
        + header
        + witness_state
    )
    f.write(record)
    pad = (-len(record)) % 8
    if pad: f.write(b'\\x00' * pad)

with open(argv[1], 'wb') as f:
    f.write(expected)
" "$in_file" "$exp_file"

  "$ZISKEMU" -e gen-out/zisk_verify_account_struct_matches.elf \
    -i "$in_file" -o "$out_file" -n 4000000 \
    >"$REPO_ROOT/gen-out/zisk_vasm_${name}.emu.log" 2>&1 || true

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
EMPTY_TRIE_HEX="56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421"
EMPTY_CODE_HEX="c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470"

FAILED=0
run_case "exact_eoa"             exact             "$ALICE" 7 1000 "$EMPTY_TRIE_HEX" "$EMPTY_CODE_HEX" || FAILED=1
run_case "exact_contract"        exact             "$ALICE" 0 0 "$EMPTY_TRIE_HEX" "ababab0102030405060708090a0b0c0d0e0f10111213141516171819aabbccdd" || FAILED=1
run_case "mismatch_nonce"        mismatch_nonce    "$ALICE" 7 1000 "$EMPTY_TRIE_HEX" "$EMPTY_CODE_HEX" || FAILED=1
run_case "mismatch_balance"      mismatch_balance  "$ALICE" 7 1000 "$EMPTY_TRIE_HEX" "$EMPTY_CODE_HEX" || FAILED=1
run_case "mismatch_storage_root" mismatch_storage_root "$ALICE" 7 1000 "$EMPTY_TRIE_HEX" "$EMPTY_CODE_HEX" || FAILED=1
run_case "mismatch_code_hash"    mismatch_code_hash "$ALICE" 7 1000 "$EMPTY_TRIE_HEX" "$EMPTY_CODE_HEX" || FAILED=1
run_case "missing_account"       missing           "$ALICE" 7 1000 "$EMPTY_TRIE_HEX" "$EMPTY_CODE_HEX" || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: verify_account_struct_matches end-to-end"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
