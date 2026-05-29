#!/usr/bin/env bash
# codegen-zisk-state-code-hash-inclusion-proof-verify-check.sh
#
# Light-client code-hash inclusion proof against a trusted
# state_root. Cheapest predicate for "does this address run
# this code?" -- especially the EOA-detection case with
# expected = EMPTY_CODE_HASH.
#
# Spec-distinguishing rows:
#
#   | account contents          | expected            | status | is_match |
#   |---------------------------|---------------------|--------|----------|
#   | EOA (code = empty)        | EMPTY_CODE_HASH     |   0    |    1     |
#   | EOA                       | hash(contract bytes)|   0    |    0     |
#   | Contract X                | keccak(X bytes)     |   0    |    1     |
#   | Contract X                | keccak(Y bytes)     |   0    |    0     |
#   | absent (spec EOA default) | EMPTY_CODE_HASH     |   1    |    1     |
#   | absent                    | any non-empty hash  |   1    |    0     |
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

echo "==> emit zisk_state_code_hash_inclusion_proof_verify ELF"
lake exe codegen --program zisk_state_code_hash_inclusion_proof_verify \
  --halt linux93 \
  -o gen-out/zisk_state_code_hash_inclusion_proof_verify

REPO_ROOT="$(pwd)"

# run_case <name> <mode> [args...]
#
#   present_match    <addr> <stored_code_mode> <expected_code_mode>
#   present_mismatch <addr> <stored_code_mode> <expected_code_mode>
#   absent           <lookup_addr> <stored_addr> <expected_code_mode>
#
#   code_mode: empty | bytes:<hex>
run_case() {
  local name="$1"; shift
  local mode="$1"; shift

  local in_file="$REPO_ROOT/gen-out/zisk_schip_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_schip_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_schip_${name}.expected"

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
    raise SystemExit('bad code_mode: ' + mode)

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
    stored_ch = resolve_code_hash(parts[1])
    expected_ch = resolve_code_hash(parts[2])
    acct = encode_account(0, 0, EMPTY_TRIE, stored_ch)
    state_root, witness_state = state_trie_one_account(addr, acct)
    is_match = 1 if stored_ch == expected_ch else 0
    if mode == 'present_match':
        assert is_match == 1, 'present_match called with mismatching codes'
    else:
        assert is_match == 0, 'present_mismatch called with matching codes'
    expected = struct.pack('<Q', 0) + struct.pack('<Q', is_match)
elif mode == 'absent':
    lookup_addr = bytes.fromhex(parts[0])
    stored_addr = bytes.fromhex(parts[1])
    expected_ch = resolve_code_hash(parts[2])
    # Build trie with stored_addr only; lookup_addr is absent.
    other_acct = encode_account(0, 0, EMPTY_TRIE, EMPTY_CODE_HASH)
    state_root, witness_state = state_trie_one_account(stored_addr, other_acct)
    addr = lookup_addr
    # Absent spec default code_hash = EMPTY_CODE_HASH.
    is_match = 1 if expected_ch == EMPTY_CODE_HASH else 0
    expected = struct.pack('<Q', 1) + struct.pack('<Q', is_match)
else:
    raise SystemExit('bad mode: ' + mode)

with open(argv[0], 'wb') as f:
    record = (
        struct.pack('<Q', len(witness_state))
        + state_root
        + addr
        + expected_ch
        + witness_state
    )
    f.write(record)
    pad = (-len(record)) % 8
    if pad: f.write(b'\\x00' * pad)

with open(argv[1], 'wb') as f:
    f.write(expected)
" "$in_file" "$exp_file"

  "$ZISKEMU" -e gen-out/zisk_state_code_hash_inclusion_proof_verify.elf \
    -i "$in_file" -o "$out_file" -n 4000000 \
    >"$REPO_ROOT/gen-out/zisk_schip_${name}.emu.log" 2>&1 || true

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
# 1) EOA present, expected EMPTY_CODE_HASH -> status 0, is_match 1.
run_case "eoa_present_match"               present_match "$ALICE" empty empty || FAILED=1
# 2) EOA present, expected contract hash -> status 0, is_match 0.
run_case "eoa_present_vs_contract"         present_mismatch "$ALICE" empty "bytes:600160005500" || FAILED=1
# 3) Contract present (X bytes), expected matches keccak(X) -> is_match 1.
run_case "contract_x_match"                present_match "$ALICE" "bytes:600160005500" "bytes:600160005500" || FAILED=1
# 4) Contract X present, expected different contract Y -> is_match 0.
run_case "contract_x_vs_y"                 present_mismatch "$ALICE" "bytes:600160005500" "bytes:6000" || FAILED=1
# 5) Contract X present, expected EMPTY_CODE_HASH -> is_match 0
#    (this proves the function distinguishes EOA from contract).
run_case "contract_x_vs_empty"             present_mismatch "$ALICE" "bytes:600160005500" empty || FAILED=1
# 6) Absent address, expected EMPTY_CODE_HASH -> status 1, is_match 1 (spec EOA default).
run_case "absent_expect_empty"             absent "$BOB" "$ALICE" empty || FAILED=1
# 7) Absent address, expected contract hash -> status 1, is_match 0.
run_case "absent_expect_contract"          absent "$BOB" "$ALICE" "bytes:600160005500" || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: state_code_hash_inclusion_proof_verify end-to-end"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
