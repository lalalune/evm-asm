#!/usr/bin/env bash
# codegen-zisk-state-account-with-spec-default-check.sh
#
# Spec-default-on-miss sibling of zisk_account_at_address.
# On a hit, identical to K28's output. On a miss, struct is
# filled with the canonical empty account (0, 0,
# EMPTY_TRIE_ROOT, EMPTY_CODE_HASH) rather than all zeros.
#
# Output (112 bytes):
#   bytes   0.. 8 : status (0=present, 1=absent-with-default, 2/3=parse fail)
#   bytes   8..16 : nonce (u64 LE)
#   bytes  16..48 : balance (32 BE)
#   bytes  48..80 : storage_root (32 B)
#   bytes  80..112: code_hash (32 B)
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

echo "==> emit zisk_state_account_with_spec_default ELF"
lake exe codegen --program zisk_state_account_with_spec_default \
  --halt linux93 \
  -o gen-out/zisk_state_account_with_spec_default

REPO_ROOT="$(pwd)"

# run_case <name> <mode> [args...]
#   present  <addr> <nonce> <balance_int> <code_mode>  (code_mode: empty|bytes:<hex>)
#   absent   <lookup_addr> <stored_addr>
#   garbage_root  <addr>
run_case() {
  local name="$1"; shift
  local mode="$1"; shift

  local in_file="$REPO_ROOT/gen-out/zisk_sasd_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_sasd_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_sasd_${name}.expected"

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

EMPTY_TRIE = bytes.fromhex('56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421')
EMPTY_CODE_HASH = bytes.fromhex('c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470')

def resolve_code_hash(mode):
    if mode == 'empty':
        return EMPTY_CODE_HASH
    if mode.startswith('bytes:'):
        return k256(bytes.fromhex(mode.split(':', 1)[1]))
    raise SystemExit('bad code_mode')

argv = sys.argv[1:]
mode = '$mode'
parts = [
$(for arg in "$@"; do printf '  %s,\n' "\"$arg\""; done)
]

def state_trie_one(addr, account_rlp):
    path = bytes_to_nibbles(k256(addr))
    leaf = leaf_node(path, account_rlp)
    return k256(leaf), build_ssz_section([leaf])

def pack_struct(status, nonce, balance, sr, ch):
    return (
        struct.pack('<Q', status)
        + struct.pack('<Q', nonce)
        + balance.to_bytes(32, 'big')
        + sr
        + ch
    )

if mode == 'present':
    addr = bytes.fromhex(parts[0])
    nonce = int(parts[1])
    balance = int(parts[2])
    ch = resolve_code_hash(parts[3])
    acct = encode_account(nonce, balance, EMPTY_TRIE, ch)
    state_root, witness_state = state_trie_one(addr, acct)
    expected = pack_struct(0, nonce, balance, EMPTY_TRIE, ch)
elif mode == 'absent':
    lookup_addr = bytes.fromhex(parts[0])
    stored_addr = bytes.fromhex(parts[1])
    other = encode_account(7, 1234, EMPTY_TRIE, EMPTY_CODE_HASH)
    state_root, witness_state = state_trie_one(stored_addr, other)
    addr = lookup_addr
    # On absent: spec default = (0, 0, EMPTY_TRIE, EMPTY_CODE_HASH).
    expected = pack_struct(1, 0, 0, EMPTY_TRIE, EMPTY_CODE_HASH)
else:
    raise SystemExit('bad mode')

with open(argv[0], 'wb') as f:
    record = (
        struct.pack('<Q', len(witness_state))
        + struct.pack('<Q', 20)
        + state_root
        + addr
        + witness_state
    )
    f.write(record)
    pad = (-len(record)) % 8
    if pad: f.write(b'\\x00' * pad)

with open(argv[1], 'wb') as f:
    f.write(expected)
" "$in_file" "$exp_file"

  "$ZISKEMU" -e gen-out/zisk_state_account_with_spec_default.elf \
    -i "$in_file" -o "$out_file" -n 4000000 \
    >"$REPO_ROOT/gen-out/zisk_sasd_${name}.emu.log" 2>&1 || true

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

ALICE="$(printf 'aa%.0s' $(seq 1 20))"
BOB="$(printf 'bb%.0s' $(seq 1 20))"

FAILED=0
# 1) EOA present.
run_case "present_eoa"               present "$ALICE" 5 1000 empty || FAILED=1
# 2) Contract present.
run_case "present_contract"          present "$ALICE" 1 0 "bytes:600160005500" || FAILED=1
# 3) Zero-balance fresh EOA present.
run_case "present_fresh_eoa"         present "$ALICE" 0 0 empty || FAILED=1
# 4) Absent -> spec default filled in.
run_case "absent_filled_with_default" absent "$BOB" "$ALICE" || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: state_account_with_spec_default end-to-end"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
