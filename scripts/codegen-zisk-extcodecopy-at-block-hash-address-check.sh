#!/usr/bin/env bash
# codegen-zisk-extcodecopy-at-block-hash-address-check.sh
#
# Hash-keyed EXTCODECOPY. From (block_hash, address,
# code_offset, length, witness.headers, witness.state,
# witness.codes) write `length` bytes of `address`'s deployed
# code (starting at `code_offset`) into a caller-supplied
# output buffer, zero-padding past the code's end.
#
# Output layout:
#   bytes  0.. 8 : status (0..6)
#   bytes  8..16 : effective length (length on success; 0 else)
#   bytes 16..(16+length) : copied bytes, zero-padded
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

echo "==> emit zisk_extcodecopy_at_block_hash_address ELF"
lake exe codegen --program zisk_extcodecopy_at_block_hash_address \
  --halt linux93 \
  -o gen-out/zisk_extcodecopy_at_block_hash_address

REPO_ROOT="$(pwd)"

# run_case <name> <mode> [args...]
#   contract <code_hex> <code_offset> <length>
#     Real contract code at ALICE; expected window per spec.
#   missing <code_offset> <length>
#     ALICE not in trie; expect (0, length, all-zero).
#   empty_code <code_offset> <length>
#     EMPTY_CODE_HASH account; expect (0, length, all-zero).
#   integrity_violation <code_hex> <code_offset> <length>
#     code_hash !=EMPTY but witness.codes empty; expect (5, 0).
#   block_hash_miss <code_hex> <code_offset> <length>
#     Wrong block_hash; expect (1, 0).
#   too_long <code_hex> <code_offset>
#     length = 257 > 256; expect (6, 0).
run_case() {
  local name="$1"; shift
  local mode="$1"; shift

  local in_file="$REPO_ROOT/gen-out/zisk_ecccbh_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_ecccbh_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_ecccbh_${name}.expected"

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

def expected_window(code, code_offset, length):
    out = bytearray(length)
    for i in range(length):
        idx = code_offset + i
        if idx < len(code):
            out[i] = code[idx]
    return bytes(out)

mode = '$mode'
parts = [
$(for arg in "$@"; do printf '  %s,\n' "\"$arg\""; done)
]
ALICE = b'\\xaa' * 20
BOB = b'\\xbb' * 20

if mode == 'contract':
    code = bytes.fromhex(parts[0])
    code_offset = int(parts[1]); length = int(parts[2])
    acct = encode_account(0, 0, EMPTY_TRIE, k256(code))
    sr, witness_state = state_trie_one(ALICE, acct)
    h0 = encode_header(sr); witness_headers = build_ssz_section([h0])
    witness_codes = build_ssz_section([code])
    block_hash = k256(h0); addr = ALICE
    expected = struct.pack('<Q', 0) + struct.pack('<Q', length) + expected_window(code, code_offset, length)
elif mode == 'missing':
    code_offset = int(parts[0]); length = int(parts[1])
    acct = encode_account(0, 0, EMPTY_TRIE, EMPTY_CODE_HASH)
    sr, witness_state = state_trie_one(BOB, acct)
    h0 = encode_header(sr); witness_headers = build_ssz_section([h0])
    witness_codes = b''
    block_hash = k256(h0); addr = ALICE
    expected = struct.pack('<Q', 0) + struct.pack('<Q', length) + bytes(length)
elif mode == 'empty_code':
    code_offset = int(parts[0]); length = int(parts[1])
    acct = encode_account(0, 0, EMPTY_TRIE, EMPTY_CODE_HASH)
    sr, witness_state = state_trie_one(ALICE, acct)
    h0 = encode_header(sr); witness_headers = build_ssz_section([h0])
    witness_codes = b''
    block_hash = k256(h0); addr = ALICE
    expected = struct.pack('<Q', 0) + struct.pack('<Q', length) + bytes(length)
elif mode == 'integrity_violation':
    code = bytes.fromhex(parts[0])
    code_offset = int(parts[1]); length = int(parts[2])
    acct = encode_account(0, 0, EMPTY_TRIE, k256(code))
    sr, witness_state = state_trie_one(ALICE, acct)
    h0 = encode_header(sr); witness_headers = build_ssz_section([h0])
    witness_codes = b''      # incomplete
    block_hash = k256(h0); addr = ALICE
    expected = struct.pack('<Q', 5) + struct.pack('<Q', 0) + bytes(length)
elif mode == 'block_hash_miss':
    code = bytes.fromhex(parts[0])
    code_offset = int(parts[1]); length = int(parts[2])
    acct = encode_account(0, 0, EMPTY_TRIE, k256(code))
    sr, witness_state = state_trie_one(ALICE, acct)
    h0 = encode_header(sr); witness_headers = build_ssz_section([h0])
    witness_codes = build_ssz_section([code])
    block_hash = b'\\xee' * 32; addr = ALICE
    expected = struct.pack('<Q', 1) + struct.pack('<Q', 0) + bytes(length)
elif mode == 'too_long':
    code = bytes.fromhex(parts[0])
    code_offset = int(parts[1])
    length = 257
    acct = encode_account(0, 0, EMPTY_TRIE, k256(code))
    sr, witness_state = state_trie_one(ALICE, acct)
    h0 = encode_header(sr); witness_headers = build_ssz_section([h0])
    witness_codes = build_ssz_section([code])
    block_hash = k256(h0); addr = ALICE
    expected = struct.pack('<Q', 6) + struct.pack('<Q', 0)  # don't compare bytes section past header
else:
    raise SystemExit('bad mode: ' + mode)

with open(sys.argv[1], 'wb') as f:
    record = (
        struct.pack('<Q', len(witness_headers))
        + struct.pack('<Q', len(witness_state))
        + struct.pack('<Q', len(witness_codes))
        + struct.pack('<Q', code_offset)
        + struct.pack('<Q', length)
        + block_hash
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

  "$ZISKEMU" -e gen-out/zisk_extcodecopy_at_block_hash_address.elf \
    -i "$in_file" -o "$out_file" -n 6000000 \
    >"$REPO_ROOT/gen-out/zisk_ecccbh_${name}.emu.log" 2>&1 || true

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
run_case "small_code_full"            contract "60006000016000526000601a526001601aF3" 0 18 || FAILED=1
run_case "small_code_mid_window"      contract "60006000016000526000601a526001601aF3" 4 8 || FAILED=1
run_case "zero_pad_past_end"          contract "60006000016000526000601a526001601aF3" 14 16 || FAILED=1
run_case "offset_far_past_end"        contract "6000" 100 8 || FAILED=1
run_case "missing_account_zeros"      missing 0 16 || FAILED=1
run_case "empty_code_zeros"           empty_code 5 32 || FAILED=1
run_case "integrity_violation"        integrity_violation "6000" 0 4 || FAILED=1
run_case "block_hash_miss"            block_hash_miss "6000" 0 8 || FAILED=1
run_case "too_long_257"               too_long "6000" 0 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: extcodecopy_at_block_hash_address end-to-end"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
