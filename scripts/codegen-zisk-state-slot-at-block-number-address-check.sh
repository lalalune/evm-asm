#!/usr/bin/env bash
# codegen-zisk-state-slot-at-block-number-address-check.sh
#
# Number-keyed e2e historical SLOAD.
#
# Output (40 bytes):
#   bytes  0.. 8 : status (0..9)
#   bytes  8..40 : u256 BE slot value
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

echo "==> emit zisk_state_slot_at_block_number_address ELF"
lake exe codegen --program zisk_state_slot_at_block_number_address \
  --halt linux93 \
  -o gen-out/zisk_state_slot_at_block_number_address

REPO_ROOT="$(pwd)"

run_case() {
  local name="$1"; shift
  local mode="$1"; shift
  local target="$1"; shift

  local in_file="$REPO_ROOT/gen-out/zisk_sasb_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_sasb_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_sasb_${name}.expected"

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

def storage_trie_one(slot_be, val_be):
    path = bytes_to_nibbles(k256(slot_be))
    leaf = leaf_node(path, rlp.encode(val_be.lstrip(b'\\x00')))
    return k256(leaf), build_ssz_section([leaf])

mode = '$mode'
target = int('$target')
ALICE = b'\\xaa' * 20
SLOT0 = (0).to_bytes(32, 'big')

if mode == 'e2e_present':
    val = (0x42).to_bytes(32, 'big')
    sr_storage, witness_storage = storage_trie_one(SLOT0, val)
    acct = encode_account(0, 0, sr_storage, EMPTY_CODE_HASH)
    sr_state, witness_state = state_trie_one(ALICE, acct)
    h_decoy = encode_header(100, b'\\xee' * 32)
    h_target = encode_header(101, sr_state)
    witness_headers = build_ssz_section([h_decoy, h_target])
    addr = ALICE; slot_idx_be = SLOT0
    expected = struct.pack('<Q', 0) + val
elif mode == 'account_absent':
    val = (0x42).to_bytes(32, 'big')
    sr_storage, witness_storage = storage_trie_one(SLOT0, val)
    BOB = b'\\xbb' * 20
    acct = encode_account(0, 0, sr_storage, EMPTY_CODE_HASH)
    sr_state, witness_state = state_trie_one(BOB, acct)
    h0 = encode_header(101, sr_state)
    witness_headers = build_ssz_section([h0])
    addr = ALICE; slot_idx_be = SLOT0  # not in trie
    expected = struct.pack('<Q', 4) + b'\\x00' * 32
elif mode == 'slot_absent':
    val = (0x42).to_bytes(32, 'big')
    SLOT_OTHER = (1).to_bytes(32, 'big')
    sr_storage, witness_storage = storage_trie_one(SLOT_OTHER, val)
    acct = encode_account(0, 0, sr_storage, EMPTY_CODE_HASH)
    sr_state, witness_state = state_trie_one(ALICE, acct)
    h0 = encode_header(101, sr_state)
    witness_headers = build_ssz_section([h0])
    addr = ALICE; slot_idx_be = SLOT0  # lookup SLOT0, but only SLOT1 exists
    expected = struct.pack('<Q', 7) + b'\\x00' * 32
elif mode == 'number_miss':
    val = (0x42).to_bytes(32, 'big')
    sr_storage, witness_storage = storage_trie_one(SLOT0, val)
    acct = encode_account(0, 0, sr_storage, EMPTY_CODE_HASH)
    sr_state, witness_state = state_trie_one(ALICE, acct)
    h0 = encode_header(100, sr_state)
    witness_headers = build_ssz_section([h0])
    addr = ALICE; slot_idx_be = SLOT0
    expected = struct.pack('<Q', 1) + b'\\x00' * 32
else:
    raise SystemExit('bad mode')

with open(sys.argv[1], 'wb') as f:
    record = (
        struct.pack('<Q', len(witness_headers))
        + struct.pack('<Q', len(witness_state))
        + struct.pack('<Q', len(witness_storage))
        + struct.pack('<Q', target)
        + addr
        + slot_idx_be
        + witness_headers
        + witness_state
        + witness_storage
    )
    f.write(record)
    pad = (-len(record)) % 8
    if pad: f.write(b'\\x00' * pad)

with open(sys.argv[2], 'wb') as f:
    f.write(expected)
" "$in_file" "$exp_file"

  "$ZISKEMU" -e gen-out/zisk_state_slot_at_block_number_address.elf \
    -i "$in_file" -o "$out_file" -n 6000000 \
    >"$REPO_ROOT/gen-out/zisk_sasb_${name}.emu.log" 2>&1 || true

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
run_case "e2e_present_at_target"        e2e_present 101 || FAILED=1
run_case "account_absent_at_target"     account_absent 101 || FAILED=1
run_case "slot_absent_at_target"        slot_absent 101 || FAILED=1
run_case "number_not_in_section"        number_miss 999 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: state_slot_at_block_number_address end-to-end"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
