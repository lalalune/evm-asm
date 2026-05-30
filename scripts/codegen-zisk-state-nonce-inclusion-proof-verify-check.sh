#!/usr/bin/env bash
# codegen-zisk-state-nonce-inclusion-proof-verify-check.sh
#
# Light-client u64 nonce inclusion proof. Completes the per-
# field family with #7197 (code_hash), #7206 (storage_root),
# #7209 (balance).
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

echo "==> emit zisk_state_nonce_inclusion_proof_verify ELF"
lake exe codegen --program zisk_state_nonce_inclusion_proof_verify \
  --halt linux93 \
  -o gen-out/zisk_state_nonce_inclusion_proof_verify

REPO_ROOT="$(pwd)"

# run_case <name> <mode> [args...]
#
#   present_match    <addr> <stored_nonce> <expected_nonce>
#   present_mismatch <addr> <stored_nonce> <expected_nonce>
#   absent           <lookup_addr> <stored_addr> <expected_nonce>
run_case() {
  local name="$1"; shift
  local mode="$1"; shift

  local in_file="$REPO_ROOT/gen-out/zisk_snip_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_snip_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_snip_${name}.expected"

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

argv = sys.argv[1:]
mode = '$mode'
parts = [
$(for arg in "$@"; do printf '  %s,\n' "\"$arg\""; done)
]

def state_trie_one_account(addr, account_rlp):
    path = bytes_to_nibbles(k256(addr))
    leaf = leaf_node(path, account_rlp)
    return k256(leaf), build_ssz_section([leaf])

if mode == 'present_match' or mode == 'present_mismatch':
    addr = bytes.fromhex(parts[0])
    stored_nonce = int(parts[1])
    expected_nonce = int(parts[2])
    acct = encode_account(stored_nonce, 0, EMPTY_TRIE, EMPTY_CODE_HASH)
    state_root, witness_state = state_trie_one_account(addr, acct)
    is_match = 1 if stored_nonce == expected_nonce else 0
    if mode == 'present_match':
        assert is_match == 1, 'present_match called with mismatching nonces'
    else:
        assert is_match == 0, 'present_mismatch called with matching nonces'
    expected = struct.pack('<Q', 0) + struct.pack('<Q', is_match)
elif mode == 'absent':
    lookup_addr = bytes.fromhex(parts[0])
    stored_addr = bytes.fromhex(parts[1])
    expected_nonce = int(parts[2])
    other_acct = encode_account(7, 1000, EMPTY_TRIE, EMPTY_CODE_HASH)
    state_root, witness_state = state_trie_one_account(stored_addr, other_acct)
    addr = lookup_addr
    is_match = 1 if expected_nonce == 0 else 0
    expected = struct.pack('<Q', 1) + struct.pack('<Q', is_match)
else:
    raise SystemExit('bad mode: ' + mode)

with open(argv[0], 'wb') as f:
    record = (
        struct.pack('<Q', len(witness_state))
        + struct.pack('<Q', expected_nonce)
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

  "$ZISKEMU" -e gen-out/zisk_state_nonce_inclusion_proof_verify.elf \
    -i "$in_file" -o "$out_file" -n 4000000 \
    >"$REPO_ROOT/gen-out/zisk_snip_${name}.emu.log" 2>&1 || true

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
MAX_U64="18446744073709551615"  # 2^64 - 1

FAILED=0
# 1) Fresh EOA (nonce=0) present, exact match.
run_case "fresh_eoa_zero_match"            present_match "$ALICE" 0 0 || FAILED=1
# 2) Small nonce present, exact match.
run_case "small_nonce_match"               present_match "$ALICE" 5 5 || FAILED=1
# 3) Max u64 nonce, exact match (edge of u64 range).
run_case "max_u64_nonce_match"             present_match "$ALICE" "$MAX_U64" "$MAX_U64" || FAILED=1
# 4) Off-by-one mismatch (replay-protection scenario).
run_case "off_by_one_mismatch"             present_mismatch "$ALICE" 42 43 || FAILED=1
# 5) Zero stored, nonzero expected -> mismatch.
run_case "zero_vs_nonzero_mismatch"        present_mismatch "$ALICE" 0 1 || FAILED=1
# 6) Absent + expected 0 -> status 1, is_match 1 (spec EOA default).
run_case "absent_expect_zero"              absent "$BOB" "$ALICE" 0 || FAILED=1
# 7) Absent + expected nonzero -> status 1, is_match 0.
run_case "absent_expect_nonzero"           absent "$BOB" "$ALICE" 42 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: state_nonce_inclusion_proof_verify end-to-end"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
