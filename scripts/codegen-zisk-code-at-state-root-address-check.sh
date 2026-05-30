#!/usr/bin/env bash
# codegen-zisk-code-at-state-root-address-check.sh
#
# Trusted-state_root bytecode extractor. Returns (offset,
# length) in witness.codes.
#
# Output (24 bytes):
#   bytes  0.. 8 : status (0..5)
#   bytes  8..16 : code_offset
#   bytes 16..24 : code_length
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

echo "==> emit zisk_code_at_state_root_address ELF"
lake exe codegen --program zisk_code_at_state_root_address \
  --halt linux93 \
  -o gen-out/zisk_code_at_state_root_address

REPO_ROOT="$(pwd)"

run_case() {
  local name="$1"; shift
  local mode="$1"; shift

  local in_file="$REPO_ROOT/gen-out/zisk_casr_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_casr_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_casr_${name}.expected"

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

def section_offset_of(elements, idx):
    return 4 * len(elements) + sum(len(e) for e in elements[:idx])

def encode_account(nonce, balance, storage_root, code_hash):
    return rlp.encode([nonce, balance, storage_root, code_hash])

EMPTY_TRIE = bytes.fromhex('56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421')
EMPTY_CODE_HASH = bytes.fromhex('c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470')

def state_trie_one(addr, acct_rlp):
    path = bytes_to_nibbles(k256(addr))
    leaf = leaf_node(path, acct_rlp)
    return k256(leaf), build_ssz_section([leaf])

mode = '$mode'
ALICE = b'\\xaa' * 20
BOB = b'\\xbb' * 20

if mode == 'contract_present':
    code = bytes.fromhex('600160005500')
    ch = k256(code)
    codes = [bytes.fromhex('6000'), code]
    witness_codes = build_ssz_section(codes)
    expected_offset = section_offset_of(codes, 1)
    expected_length = len(code)
    acct = encode_account(1, 0, EMPTY_TRIE, ch)
    state_root, witness_state = state_trie_one(ALICE, acct)
    addr = ALICE
    expected = (
        struct.pack('<Q', 0)
        + struct.pack('<Q', expected_offset)
        + struct.pack('<Q', expected_length)
    )
elif mode == 'eoa_empty':
    acct = encode_account(0, 0, EMPTY_TRIE, EMPTY_CODE_HASH)
    state_root, witness_state = state_trie_one(ALICE, acct)
    witness_codes = build_ssz_section([])
    addr = ALICE
    expected = struct.pack('<Q', 2) + struct.pack('<Q', 0) + struct.pack('<Q', 0)
elif mode == 'account_absent':
    acct = encode_account(0, 0, EMPTY_TRIE, EMPTY_CODE_HASH)
    state_root, witness_state = state_trie_one(BOB, acct)
    witness_codes = build_ssz_section([])
    addr = ALICE
    expected = struct.pack('<Q', 1) + struct.pack('<Q', 0) + struct.pack('<Q', 0)
elif mode == 'code_hash_not_in_codes':
    code = bytes.fromhex('6042')
    ch = k256(code)
    acct = encode_account(1, 0, EMPTY_TRIE, ch)
    state_root, witness_state = state_trie_one(ALICE, acct)
    decoy = bytes.fromhex('1234')
    witness_codes = build_ssz_section([decoy])
    addr = ALICE
    expected = struct.pack('<Q', 5) + struct.pack('<Q', 0) + struct.pack('<Q', 0)
else:
    raise SystemExit('bad mode')

with open(sys.argv[1], 'wb') as f:
    record = (
        struct.pack('<Q', len(witness_state))
        + struct.pack('<Q', len(witness_codes))
        + state_root
        + addr
        + witness_state
        + witness_codes
    )
    f.write(record)
    pad = (-len(record)) % 8
    if pad: f.write(b'\\x00' * pad)

with open(sys.argv[2], 'wb') as f:
    f.write(expected)
" "$in_file" "$exp_file"

  "$ZISKEMU" -e gen-out/zisk_code_at_state_root_address.elf \
    -i "$in_file" -o "$out_file" -n 6000000 \
    >"$REPO_ROOT/gen-out/zisk_casr_${name}.emu.log" 2>&1 || true

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
run_case "contract_present"             contract_present || FAILED=1
run_case "eoa_empty_code"               eoa_empty || FAILED=1
run_case "account_absent"               account_absent || FAILED=1
run_case "code_hash_not_in_codes"       code_hash_not_in_codes || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: code_at_state_root_address end-to-end"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
