#!/usr/bin/env bash
# codegen-zisk-nonce-at-header-state-root-check.sh
#
# Witness-side getter for account.nonce as a u64. Returns 0 for
# absent accounts (same "absent → 0" flattening as BALANCE / SLOAD).
#
# Output (16 bytes):
#   bytes  0.. 8 : status (0 / 2 / 3 / 4)
#   bytes  8..16 : nonce (u64 LE; 0 on absent)
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

echo "==> emit zisk_nonce_at_header_state_root ELF"
lake exe codegen --program zisk_nonce_at_header_state_root \
  --halt linux93 \
  -o gen-out/zisk_nonce_at_header_state_root

REPO_ROOT="$(pwd)"

run_case() {
  local name="$1"; shift
  local mode="$1"; shift

  local in_file="$REPO_ROOT/gen-out/zisk_nonce_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_nonce_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_nonce_${name}.expected"

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

def build_state_trie(addr, account_rlp):
    path = bytes_to_nibbles(k256(addr))
    leaf = leaf_node(path, account_rlp)
    return k256(leaf), build_ssz_section([leaf])

if mode == 'account':
    addr = bytes.fromhex(parts[0])
    nonce = int(parts[1])
    balance = int(parts[2])
    account = encode_account(nonce, balance, EMPTY_TRIE, EMPTY_CODE)
    state_root, witness_state = build_state_trie(addr, account)
    header = encode_header(state_root)
    expected = struct.pack('<Q', 0) + struct.pack('<Q', nonce)
elif mode == 'missing':
    lookup_addr = bytes.fromhex(parts[0])
    stored_addr = bytes.fromhex(parts[1])
    account = encode_account(42, 0, EMPTY_TRIE, EMPTY_CODE)
    state_root, witness_state = build_state_trie(stored_addr, account)
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

  "$ZISKEMU" -e gen-out/zisk_nonce_at_header_state_root.elf \
    -i "$in_file" -o "$out_file" -n 4000000 \
    >"$REPO_ROOT/gen-out/zisk_nonce_${name}.emu.log" 2>&1 || true

  local exp_size; exp_size="$(stat -c%s "$exp_file")"
  local actual expected
  actual="$(xxd -p -l "$exp_size" "$out_file" 2>/dev/null | tr -d '\n')"
  expected="$(xxd -p -l "$exp_size" "$exp_file" 2>/dev/null | tr -d '\n')"

  if [[ "$actual" == "$expected" ]]; then
    printf "  %-26s OK   %d bytes match\n" "$name" "$exp_size"
    return 0
  else
    printf "  %-26s FAIL\n    expected: %s\n    actual:   %s\n" \
      "$name" "$expected" "$actual"
    return 1
  fi
}

ALICE="$(printf 'aa%.0s' $(seq 1 20))"
BOB="$(printf 'bb%.0s' $(seq 1 20))"

FAILED=0
run_case "nonce_zero"           account "$ALICE" 0 0 || FAILED=1
run_case "nonce_one"            account "$ALICE" 1 0 || FAILED=1
run_case "nonce_typical"        account "$ALICE" 42 1000000000000000000 || FAILED=1
run_case "nonce_u64_max"        account "$ALICE" 18446744073709551615 0 || FAILED=1
# Spec-defining flatten: missing account returns 0 (NOT an error).
run_case "missing_account"      missing "$BOB" "$ALICE" || FAILED=1
run_case "garbage_header"       garbage_header "$ALICE" || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: nonce_at_header_state_root end-to-end"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
