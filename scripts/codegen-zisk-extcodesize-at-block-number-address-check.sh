#!/usr/bin/env bash
# codegen-zisk-extcodesize-at-block-number-address-check.sh
#
# Number-keyed EXTCODESIZE primitive. First EVM opcode at
# the block_number key level.
#
# Output (16 bytes):
#   bytes  0.. 8 : status (0..6)
#   bytes  8..16 : code length (u64; 0 for missing/empty)
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

echo "==> emit zisk_extcodesize_at_block_number_address ELF"
lake exe codegen --program zisk_extcodesize_at_block_number_address \
  --halt linux93 \
  -o gen-out/zisk_extcodesize_at_block_number_address

REPO_ROOT="$(pwd)"

# run_case <name> <mode> <target> [args...]
run_case() {
  local name="$1"; shift
  local mode="$1"; shift
  local target="$1"; shift

  local in_file="$REPO_ROOT/gen-out/zisk_ecsbn_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_ecsbn_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_ecsbn_${name}.expected"

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

def encode_header(number_val, state_root):
    if number_val == 0:
        number_field = b''
    else:
        nbytes = (number_val.bit_length() + 7) // 8
        number_field = number_val.to_bytes(nbytes, 'big')
    fields = [
        b'\\x11'*32, b'\\x22'*32, b'\\x33'*20, state_root, b'\\x55'*32,
        b'\\x66'*32, b'\\x00'*256, b'', number_field, b'\\x83\\xff\\xff\\xff',
        b'', b'\\x83\\x01\\x02\\x03', b'', b'\\x77'*32, b'\\x00'*8,
    ]
    return rlp.encode(fields)

EMPTY_TRIE = bytes.fromhex('56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421')
EMPTY_CODE_HASH = bytes.fromhex('c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470')

def state_trie_one(addr, acct_rlp):
    path = bytes_to_nibbles(k256(addr))
    leaf = leaf_node(path, acct_rlp)
    return k256(leaf), build_ssz_section([leaf])

mode = '$mode'
target = int('$target')
parts = '$parts'.split('|')
ALICE = b'\\xaa' * 20
BOB = b'\\xbb' * 20

if mode == 'contract':
    code = bytes.fromhex(parts[0])
    code_hash = k256(code)
    acct = encode_account(0, 0, EMPTY_TRIE, code_hash)
    sr, witness_state = state_trie_one(ALICE, acct)
    h0 = encode_header(100, b'\\xee'*32)
    h1 = encode_header(101, sr)
    witness_headers = build_ssz_section([h0, h1])
    witness_codes = build_ssz_section([code])
    addr = ALICE
    expected = struct.pack('<Q', 0) + struct.pack('<Q', len(code))
elif mode == 'empty_code_present':
    acct = encode_account(7, 0, EMPTY_TRIE, EMPTY_CODE_HASH)
    sr, witness_state = state_trie_one(ALICE, acct)
    h0 = encode_header(101, sr)
    witness_headers = build_ssz_section([h0])
    witness_codes = b''
    addr = ALICE
    expected = struct.pack('<Q', 0) + struct.pack('<Q', 0)
elif mode == 'missing_account':
    code = bytes.fromhex(parts[0])
    code_hash = k256(code)
    acct = encode_account(0, 0, EMPTY_TRIE, code_hash)
    sr, witness_state = state_trie_one(BOB, acct)
    h0 = encode_header(101, sr)
    witness_headers = build_ssz_section([h0])
    witness_codes = build_ssz_section([code])
    addr = ALICE
    expected = struct.pack('<Q', 0) + struct.pack('<Q', 0)
elif mode == 'integrity_violation':
    code = bytes.fromhex(parts[0])
    code_hash = k256(code)
    acct = encode_account(0, 0, EMPTY_TRIE, code_hash)
    sr, witness_state = state_trie_one(ALICE, acct)
    h0 = encode_header(101, sr)
    witness_headers = build_ssz_section([h0])
    witness_codes = b''  # incomplete
    addr = ALICE
    expected = struct.pack('<Q', 6) + struct.pack('<Q', 0)
elif mode == 'number_miss':
    code = bytes.fromhex(parts[0])
    code_hash = k256(code)
    acct = encode_account(0, 0, EMPTY_TRIE, code_hash)
    sr, witness_state = state_trie_one(ALICE, acct)
    h0 = encode_header(100, sr)
    witness_headers = build_ssz_section([h0])
    witness_codes = build_ssz_section([code])
    addr = ALICE
    expected = struct.pack('<Q', 1) + struct.pack('<Q', 0)
else:
    raise SystemExit('bad mode: ' + mode)

with open(sys.argv[1], 'wb') as f:
    record = (
        struct.pack('<Q', len(witness_headers))
        + struct.pack('<Q', len(witness_state))
        + struct.pack('<Q', len(witness_codes))
        + struct.pack('<Q', target)
        + addr
        + witness_headers
        + witness_state
        + witness_codes
    )
    f.write(record)
    pad = (-len(record)) % 8
    if pad: f.write(b'\\x00' * pad)

with open(sys.argv[2], 'wb') as f:
    f.write(expected)
" "$in_file" "$exp_file"

  "$ZISKEMU" -e gen-out/zisk_extcodesize_at_block_number_address.elf \
    -i "$in_file" -o "$out_file" -n 6000000 \
    >"$REPO_ROOT/gen-out/zisk_ecsbn_${name}.emu.log" 2>&1 || true

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

FAILED=0
parts="6000"                                     run_case "contract_tiny_code"        contract 101 || FAILED=1
parts="60006000016000526000601a526001601aF3"     run_case "contract_18b_code"         contract 101 || FAILED=1
parts=""                                         run_case "empty_code_eoa"            empty_code_present 101 || FAILED=1
parts="6000"                                     run_case "missing_account_zero"      missing_account 101 || FAILED=1
parts="6000"                                     run_case "integrity_violation"       integrity_violation 101 || FAILED=1
parts="6000"                                     run_case "number_not_in_section"     number_miss 999 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: extcodesize_at_block_number_address end-to-end"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
