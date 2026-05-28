#!/usr/bin/env bash
# codegen-zisk-code-at-header-state-root-check.sh
#
# Fifth storage-proof step (code-hash side of the account):
# from a parent header RLP, walk the state trie to an account
# leaf, then look up `account.code_hash` in `witness.codes`.
#
# Composes header_extract_state_root (K201), account_at_address
# (K28), and witness_lookup_by_hash (K19). Returns:
#   0  found in both trie and codes section (offset+len at OUT+8)
#   1  account not in state trie
#   2  state-trie mpt parse error
#   3  account_decode failure
#   4  header parse / state_root size fail
#   5  code_hash not found in witness.codes
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

echo "==> emit zisk_code_at_header_state_root ELF"
lake exe codegen --program zisk_code_at_header_state_root \
  --halt linux93 \
  -o gen-out/zisk_code_at_header_state_root

REPO_ROOT="$(pwd)"

# run_case <name> <mode> [args...]
#
#   match <addr> <code_hex> <nonce> <balance> [extra_codes_csv]
#     Single-leaf state trie at addr; code_hash field of the
#     account is keccak(code); witness.codes = [code] (plus any
#     comma-separated extras for non-trivial section layout).
#     Expected (0, offset, length).
#
#   code_miss <addr> <stored_code_hex> <hash_field_hex> <nonce> <balance>
#     account.code_hash is hash_field_hex (NOT keccak of stored_code).
#     witness.codes = [stored_code]. Expected status 5.
#
#   acct_miss <lookup_addr> <stored_addr> <code_hex> <nonce> <balance>
#     state trie has stored_addr; lookup uses lookup_addr.
#     Expected status 1.
#
#   garbage_header <addr> <code_hex>
#     1-byte invalid header. Expected status 4.
run_case() {
  local name="$1"; shift
  local mode="$1"; shift

  local in_file="$REPO_ROOT/gen-out/zisk_cahsr_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_cahsr_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_cahsr_${name}.expected"

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

argv = sys.argv[1:]
mode = '$mode'
parts = [
$(for arg in "$@"; do printf '  %s,\n' "\"$arg\""; done)
]

def build_state_with_account(addr, account_rlp):
    path = bytes_to_nibbles(k256(addr))
    leaf = leaf_node(path, account_rlp)
    return k256(leaf), build_ssz_section([leaf])

def offset_length_of(section, target_hash):
    if not section:
        return None
    n = struct.unpack('<I', section[0:4])[0] // 4
    offsets = [struct.unpack('<I', section[4*i:4*i+4])[0] for i in range(n)]
    bounds = offsets + [len(section)]
    for i in range(n):
        elem = section[bounds[i]:bounds[i+1]]
        if k256(elem) == target_hash:
            return (bounds[i], bounds[i+1] - bounds[i])
    return None

if mode == 'match':
    addr = bytes.fromhex(parts[0])
    code = bytes.fromhex(parts[1])
    nonce = int(parts[2])
    balance = int(parts[3])
    extra_csv = parts[4] if len(parts) > 4 else ''
    extra_codes = [bytes.fromhex(p) for p in extra_csv.split(',') if p]
    code_hash = k256(code)
    account = encode_account(nonce, balance, EMPTY_TRIE, code_hash)
    state_root, witness_state = build_state_with_account(addr, account)
    codes_list = extra_codes + [code]
    witness_codes = build_ssz_section(codes_list)
    ol = offset_length_of(witness_codes, code_hash)
    assert ol is not None
    header = encode_header(state_root)
    expected = struct.pack('<Q', 0) + struct.pack('<Q', ol[0]) + struct.pack('<Q', ol[1])
elif mode == 'code_miss':
    addr = bytes.fromhex(parts[0])
    stored_code = bytes.fromhex(parts[1])
    hash_field = bytes.fromhex(parts[2])
    nonce = int(parts[3])
    balance = int(parts[4])
    account = encode_account(nonce, balance, EMPTY_TRIE, hash_field)
    state_root, witness_state = build_state_with_account(addr, account)
    witness_codes = build_ssz_section([stored_code])
    header = encode_header(state_root)
    expected = struct.pack('<Q', 5) + b'\\x00' * 16
elif mode == 'acct_miss':
    lookup_addr = bytes.fromhex(parts[0])
    stored_addr = bytes.fromhex(parts[1])
    code = bytes.fromhex(parts[2])
    nonce = int(parts[3])
    balance = int(parts[4])
    code_hash = k256(code)
    account = encode_account(nonce, balance, EMPTY_TRIE, code_hash)
    state_root, witness_state = build_state_with_account(stored_addr, account)
    witness_codes = build_ssz_section([code])
    addr = lookup_addr
    header = encode_header(state_root)
    expected = struct.pack('<Q', 1) + b'\\x00' * 16
elif mode == 'garbage_header':
    addr = bytes.fromhex(parts[0])
    _code = bytes.fromhex(parts[1])
    witness_state = b''
    witness_codes = b''
    header = b'\\x00'
    expected = struct.pack('<Q', 4) + b'\\x00' * 16
else:
    raise SystemExit('bad mode: ' + mode)

with open(argv[0], 'wb') as f:
    record = (
        struct.pack('<Q', len(header))
        + struct.pack('<Q', len(witness_state))
        + struct.pack('<Q', len(witness_codes))
        + addr
        + header
        + witness_state
        + witness_codes
    )
    f.write(record)
    pad = (-len(record)) % 8
    if pad: f.write(b'\\x00' * pad)

with open(argv[1], 'wb') as f:
    f.write(expected)
" "$in_file" "$exp_file"

  "$ZISKEMU" -e gen-out/zisk_code_at_header_state_root.elf \
    -i "$in_file" -o "$out_file" -n 4000000 \
    >"$REPO_ROOT/gen-out/zisk_cahsr_${name}.emu.log" 2>&1 || true

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
# Tiny code (PUSH1 0; STOP)
run_case "match_tiny_code"           match "$ALICE" "6000" 0 0 || FAILED=1
# Longer code with a few extra codes ahead of it (so offset > 4*N).
run_case "match_with_padding_codes"  match "$ALICE" "60006000016000526000601a526001601aF3" 42 1000000000000000000 "deadbeef,aa55aa55" || FAILED=1
# code_miss: hash_field doesn't match any code in section.
run_case "code_miss_unrelated_hash"  code_miss "$ALICE" "6000" "cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc" 0 0 || FAILED=1
# acct_miss: account not at lookup address.
run_case "acct_miss_other_addr"      acct_miss "$BOB" "$ALICE" "6000" 0 0 || FAILED=1
# garbage_header.
run_case "garbage_header"            garbage_header "$ALICE" "6000" || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: code_at_header_state_root end-to-end"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
