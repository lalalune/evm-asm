#!/usr/bin/env bash
# codegen-zisk-extcodesize-at-block-hash-address-check.sh
#
# Hash-keyed EXTCODESIZE. From (block_hash, address, witness.headers,
# witness.state, witness.codes), return the u64 byte length that
# EXTCODESIZE(address) would push when executed against the block
# named by block_hash:
#   * 0 if the account doesn't exist
#   * 0 if account.code_hash == EMPTY_CODE_HASH
#   * len(witness.codes[i]) where keccak(codes[i]) == account.code_hash
#
# Composes K19 (witness.headers) + K201 + K28 + K19 (witness.codes).
#
# Output (16 bytes):
#   bytes  0.. 8 : status
#       0 success
#       1 block_hash not in witness.headers
#       2 matched header parse / state_root size fail
#       3 state-trie mpt parse error
#       4 account_decode failure
#       5 code_hash != EMPTY but not in witness.codes
#   bytes  8..16 : code length (u64)
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

echo "==> emit zisk_extcodesize_at_block_hash_address ELF"
lake exe codegen --program zisk_extcodesize_at_block_hash_address \
  --halt linux93 \
  -o gen-out/zisk_extcodesize_at_block_hash_address

REPO_ROOT="$(pwd)"

# run_case <name> <mode> [args...]
#   contract <addr> <nonce> <balance> <code_hex>
#     -> (0, len(code_bytes))
#   empty_code_present <addr> <nonce> <balance>
#     -> (0, 0)
#   missing_account <lookup_addr> <stored_addr> <nonce> <balance> <code_hex>
#     -> (0, 0)
#   integrity_violation <addr> <nonce> <balance> <code_hex>
#     -> (5, 0)
#   block_hash_miss <addr> <nonce> <balance> <code_hex>
#     -> (1, 0)
run_case() {
  local name="$1"; shift
  local mode="$1"; shift

  local in_file="$REPO_ROOT/gen-out/zisk_ecsabh_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_ecsabh_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_ecsabh_${name}.expected"

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

argv = sys.argv[1:]
mode = '$mode'
parts = [
$(for arg in "$@"; do printf '  %s,\n' "\"$arg\""; done)
]

if mode == 'contract':
    addr = bytes.fromhex(parts[0])
    nonce = int(parts[1]); balance = int(parts[2])
    code = bytes.fromhex(parts[3])
    code_hash = k256(code)
    acct = encode_account(nonce, balance, EMPTY_TRIE, code_hash)
    sr, witness_state = state_trie_one(addr, acct)
    h0 = encode_header(sr); witness_headers = build_ssz_section([h0])
    witness_codes = build_ssz_section([code])
    block_hash = k256(h0)
    expected = struct.pack('<Q', 0) + struct.pack('<Q', len(code))
elif mode == 'empty_code_present':
    addr = bytes.fromhex(parts[0])
    nonce = int(parts[1]); balance = int(parts[2])
    acct = encode_account(nonce, balance, EMPTY_TRIE, EMPTY_CODE_HASH)
    sr, witness_state = state_trie_one(addr, acct)
    h0 = encode_header(sr); witness_headers = build_ssz_section([h0])
    witness_codes = b''
    block_hash = k256(h0)
    expected = struct.pack('<Q', 0) + struct.pack('<Q', 0)
elif mode == 'missing_account':
    lookup_addr = bytes.fromhex(parts[0])
    stored_addr = bytes.fromhex(parts[1])
    nonce = int(parts[2]); balance = int(parts[3])
    code = bytes.fromhex(parts[4])
    code_hash = k256(code)
    acct = encode_account(nonce, balance, EMPTY_TRIE, code_hash)
    sr, witness_state = state_trie_one(stored_addr, acct)
    h0 = encode_header(sr); witness_headers = build_ssz_section([h0])
    witness_codes = build_ssz_section([code])
    addr = lookup_addr
    block_hash = k256(h0)
    expected = struct.pack('<Q', 0) + struct.pack('<Q', 0)
elif mode == 'integrity_violation':
    addr = bytes.fromhex(parts[0])
    nonce = int(parts[1]); balance = int(parts[2])
    code = bytes.fromhex(parts[3])
    code_hash = k256(code)
    acct = encode_account(nonce, balance, EMPTY_TRIE, code_hash)
    sr, witness_state = state_trie_one(addr, acct)
    h0 = encode_header(sr); witness_headers = build_ssz_section([h0])
    witness_codes = b''     # incomplete
    block_hash = k256(h0)
    expected = struct.pack('<Q', 5) + struct.pack('<Q', 0)
elif mode == 'block_hash_miss':
    addr = bytes.fromhex(parts[0])
    nonce = int(parts[1]); balance = int(parts[2])
    code = bytes.fromhex(parts[3])
    code_hash = k256(code)
    acct = encode_account(nonce, balance, EMPTY_TRIE, code_hash)
    sr, witness_state = state_trie_one(addr, acct)
    h0 = encode_header(sr); witness_headers = build_ssz_section([h0])
    witness_codes = build_ssz_section([code])
    block_hash = b'\\xee' * 32
    expected = struct.pack('<Q', 1) + struct.pack('<Q', 0)
else:
    raise SystemExit('bad mode: ' + mode)

with open(argv[0], 'wb') as f:
    record = (
        struct.pack('<Q', len(witness_headers))
        + struct.pack('<Q', len(witness_state))
        + struct.pack('<Q', len(witness_codes))
        + block_hash
        + addr
        + witness_headers
        + witness_state
        + witness_codes
    )
    f.write(record)
    pad = (-len(record)) % 8
    if pad: f.write(b'\\x00' * pad)

with open(argv[1], 'wb') as f:
    f.write(expected)
" "$in_file" "$exp_file"

  "$ZISKEMU" -e gen-out/zisk_extcodesize_at_block_hash_address.elf \
    -i "$in_file" -o "$out_file" -n 6000000 \
    >"$REPO_ROOT/gen-out/zisk_ecsabh_${name}.emu.log" 2>&1 || true

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
run_case "contract_tiny_code"           contract "$ALICE" 0 0 "6000" || FAILED=1
run_case "contract_18b_code"            contract "$ALICE" 42 1000000000000000000 "60006000016000526000601a526001601aF3" || FAILED=1
run_case "empty_code_eoa_with_value"    empty_code_present "$ALICE" 1 1000000000000000000 || FAILED=1
run_case "fully_empty_account"          empty_code_present "$ALICE" 0 0 || FAILED=1
run_case "missing_account_zero"         missing_account "$BOB" "$ALICE" 0 0 "6000" || FAILED=1
run_case "integrity_violation_no_codes" integrity_violation "$ALICE" 0 0 "6000" || FAILED=1
run_case "block_hash_miss"              block_hash_miss "$ALICE" 0 0 "6000" || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: extcodesize_at_block_hash_address end-to-end"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
