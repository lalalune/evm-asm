#!/usr/bin/env bash
# codegen-zisk-verify-code-hash-matches-check.sh
#
# Hash the caller-supplied code bytes via keccak256 and compare
# against account.code_hash at the resolved trie leaf. Returns
# is_match = 1 iff equal.
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

echo "==> emit zisk_verify_code_hash_matches ELF"
lake exe codegen --program zisk_verify_code_hash_matches \
  --halt linux93 \
  -o gen-out/zisk_verify_code_hash_matches

REPO_ROOT="$(pwd)"

# run_case <name> <mode> [args...]
#   exact <addr> <stored_code_hex> <expected_code_hex>
#     account has code = stored_code_hex; caller provides expected_code_hex.
#   eoa_empty_expected <addr>
#     account is EOA (code_hash = EMPTY_CODE_HASH); expected is empty.
#   missing <lookup_addr> <stored_addr>
#     status 1; is_match 0.
#   garbage_header <addr>
#     status 4.
run_case() {
  local name="$1"; shift
  local mode="$1"; shift

  local in_file="$REPO_ROOT/gen-out/zisk_vchm_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_vchm_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_vchm_${name}.expected"

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

def build_state_with_account(addr, nonce, balance, code_hash):
    account = encode_account(nonce, balance, EMPTY_TRIE, code_hash)
    path = bytes_to_nibbles(k256(addr))
    leaf = leaf_node(path, account)
    return k256(leaf), build_ssz_section([leaf])

if mode == 'exact':
    addr = bytes.fromhex(parts[0])
    stored_code = bytes.fromhex(parts[1])
    expected_code = bytes.fromhex(parts[2])
    stored_hash = k256(stored_code)
    state_root, witness_state = build_state_with_account(addr, 0, 0, stored_hash)
    header = encode_header(state_root)
    expected_status = 0
    expected_is_match = 1 if (k256(expected_code) == stored_hash) else 0
elif mode == 'eoa_empty_expected':
    addr = bytes.fromhex(parts[0])
    expected_code = b''
    state_root, witness_state = build_state_with_account(addr, 0, 0, EMPTY_CODE_HASH)
    header = encode_header(state_root)
    expected_status = 0
    expected_is_match = 1
elif mode == 'missing':
    lookup_addr = bytes.fromhex(parts[0])
    stored_addr = bytes.fromhex(parts[1])
    expected_code = b'\\x60\\x00'
    state_root, witness_state = build_state_with_account(stored_addr, 0, 0, EMPTY_CODE_HASH)
    header = encode_header(state_root)
    addr = lookup_addr
    expected_status = 1
    expected_is_match = 0
elif mode == 'garbage_header':
    addr = bytes.fromhex(parts[0])
    expected_code = b'\\x60\\x00'
    witness_state = b''
    header = b'\\x00'
    expected_status = 4
    expected_is_match = 0
else:
    raise SystemExit('bad mode: ' + mode)

expected = struct.pack('<Q', expected_status) + struct.pack('<Q', expected_is_match)

with open(argv[0], 'wb') as f:
    record = (
        struct.pack('<Q', len(header))
        + struct.pack('<Q', len(witness_state))
        + struct.pack('<Q', len(expected_code))
        + addr
        + header
        + expected_code
        + witness_state
    )
    f.write(record)
    pad = (-len(record)) % 8
    if pad: f.write(b'\\x00' * pad)

with open(argv[1], 'wb') as f:
    f.write(expected)
" "$in_file" "$exp_file"

  "$ZISKEMU" -e gen-out/zisk_verify_code_hash_matches.elf \
    -i "$in_file" -o "$out_file" -n 4000000 \
    >"$REPO_ROOT/gen-out/zisk_vchm_${name}.emu.log" 2>&1 || true

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
# Exact: account stores code C, expected = C.
run_case "match_short_code"         exact "$ALICE" "6000" "6000" || FAILED=1
run_case "match_longer_code"        exact "$ALICE" "60006000016000526000601a526001601aF3" "60006000016000526000601a526001601aF3" || FAILED=1
# Mismatch: stored and expected differ.
run_case "mismatch"                 exact "$ALICE" "6000" "6001" || FAILED=1
# Spec-defining: EOA with empty expected code -> matches via EMPTY_CODE_HASH.
run_case "eoa_empty_match"          eoa_empty_expected "$ALICE" || FAILED=1
# Missing account.
run_case "missing_account"          missing "$BOB" "$ALICE" || FAILED=1
# Garbage header.
run_case "garbage_header"           garbage_header "$ALICE" || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: verify_code_hash_matches end-to-end"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
