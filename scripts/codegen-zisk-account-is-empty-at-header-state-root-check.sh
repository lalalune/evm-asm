#!/usr/bin/env bash
# codegen-zisk-account-is-empty-at-header-state-root-check.sh
#
# Witness-side EIP-161 account_is_empty predicate. Returns 1 iff
# the account is present in the state trie AND fully empty
# (nonce=0, balance=0, code_hash=EMPTY_CODE_HASH).
#
# Completes the boolean-predicate trio with:
#   * account_exists  (presence only; ignores contents)
#   * has_code_or_nonce  (EIP-684; nonce OR code, no balance)
#   * account_is_empty   (EIP-161; nonce AND balance AND code all
#                         zero, present in trie)
#
# Spec-distinguishing rows:
#
#   | account contents             | exists | EIP-684 | EIP-161 |
#   |------------------------------|--------|---------|---------|
#   | fully empty (in trie)        |   1    |    0    |    1    |
#   | balance only                 |   1    |    0    |    0    |
#   | nonce only                   |   1    |    1    |    0    |
#   | contract                     |   1    |    1    |    0    |
#   | (not in trie)                |   0    |    0    |    0    |
#
# Output (16 bytes):
#   bytes  0.. 8 : status (0 / 2 / 3 / 4)
#   bytes  8..16 : predicate (u64; 0 or 1)
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

echo "==> emit zisk_account_is_empty_at_header_state_root ELF"
lake exe codegen --program zisk_account_is_empty_at_header_state_root \
  --halt linux93 \
  -o gen-out/zisk_account_is_empty_at_header_state_root

REPO_ROOT="$(pwd)"

# run_case <name> <mode> [args...]
#
#   account <addr> <nonce> <balance> <code_mode>  -- code_mode: empty | contract:<hex>
#   missing <lookup_addr> <stored_addr>
#   garbage_header <addr>
run_case() {
  local name="$1"; shift
  local mode="$1"; shift

  local in_file="$REPO_ROOT/gen-out/zisk_aie_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_aie_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_aie_${name}.expected"

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

def build_state_trie(addr, account_rlp):
    path = bytes_to_nibbles(k256(addr))
    leaf = leaf_node(path, account_rlp)
    return k256(leaf), build_ssz_section([leaf])

def resolve_code_hash(mode):
    if mode == 'empty':
        return EMPTY_CODE_HASH
    if mode.startswith('contract:'):
        return k256(bytes.fromhex(mode.split(':', 1)[1]))
    raise SystemExit('bad code_mode: ' + mode)

if mode == 'account':
    addr = bytes.fromhex(parts[0])
    nonce = int(parts[1])
    balance = int(parts[2])
    code_hash = resolve_code_hash(parts[3])
    account = encode_account(nonce, balance, EMPTY_TRIE, code_hash)
    state_root, witness_state = build_state_trie(addr, account)
    header = encode_header(state_root)
    # EIP-161 emptiness: nonce==0 AND balance==0 AND code_hash==EMPTY_CODE_HASH.
    pred = 1 if (nonce == 0 and balance == 0 and code_hash == EMPTY_CODE_HASH) else 0
    expected = struct.pack('<Q', 0) + struct.pack('<Q', pred)
elif mode == 'missing':
    lookup_addr = bytes.fromhex(parts[0])
    stored_addr = bytes.fromhex(parts[1])
    account = encode_account(0, 0, EMPTY_TRIE, EMPTY_CODE_HASH)
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

  "$ZISKEMU" -e gen-out/zisk_account_is_empty_at_header_state_root.elf \
    -i "$in_file" -o "$out_file" -n 4000000 \
    >"$REPO_ROOT/gen-out/zisk_aie_${name}.emu.log" 2>&1 || true

  local exp_size; exp_size="$(stat -c%s "$exp_file")"
  local actual expected
  actual="$(xxd -p -l "$exp_size" "$out_file" 2>/dev/null | tr -d '\n')"
  expected="$(xxd -p -l "$exp_size" "$exp_file" 2>/dev/null | tr -d '\n')"

  if [[ "$actual" == "$expected" ]]; then
    printf "  %-32s OK   %d bytes match\n" "$name" "$exp_size"
    return 0
  else
    printf "  %-32s FAIL\n    expected: %s\n    actual:   %s\n" \
      "$name" "$expected" "$actual"
    return 1
  fi
}

ALICE="$(printf 'aa%.0s' $(seq 1 20))"
BOB="$(printf 'bb%.0s' $(seq 1 20))"

FAILED=0
# All five distinguishing rows from the table in the function comment:
# 1) fully empty in trie -> predicate 1 (this row distinguishes from EIP-684).
run_case "fully_empty_in_trie"            account "$ALICE" 0 0 "empty" || FAILED=1
# 2) balance only -> predicate 0 (this row distinguishes from account_exists).
run_case "balance_only"                   account "$ALICE" 0 1000000000000000000 "empty" || FAILED=1
# 3) nonce only -> predicate 0.
run_case "nonce_only"                     account "$ALICE" 1 0 "empty" || FAILED=1
# 4) contract -> predicate 0.
run_case "contract_nonzero_state"         account "$ALICE" 7 1000 "contract:6000" || FAILED=1
# Hybrid: nonzero everything -> predicate 0.
run_case "fully_active"                   account "$ALICE" 42 1000 "contract:6000" || FAILED=1
# 5) account not in trie -> predicate 0.
run_case "missing_account"                missing "$BOB" "$ALICE" || FAILED=1
# Structural failure.
run_case "garbage_header"                 garbage_header "$ALICE" || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: account_is_empty_at_header_state_root (EIP-161) end-to-end"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
