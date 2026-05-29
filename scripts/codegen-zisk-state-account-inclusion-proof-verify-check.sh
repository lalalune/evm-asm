#!/usr/bin/env bash
# codegen-zisk-state-account-inclusion-proof-verify-check.sh
#
# Light-client account-inclusion-proof primitive. Distinct from
# verify_account_struct_matches (PR #7187): takes a trusted
# state_root DIRECTLY rather than walking a header.
#
# Spec-distinguishing rows:
#
#   | account in trie? | walked struct           | expected             | status | is_match |
#   |------------------|-------------------------|----------------------|--------|----------|
#   | yes              | S                       | S                    |   0    |    1     |
#   | yes              | S                       | S' != S              |   0    |    0     |
#   | no               | (empty default per spec)| empty_default        |   1    |    1     |
#   | no               | (empty default per spec)| anything else        |   1    |    0     |
#   | mpt parse fail   |     -                   |    -                 |  2/3   |    0     |
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

echo "==> emit zisk_state_account_inclusion_proof_verify ELF"
lake exe codegen --program zisk_state_account_inclusion_proof_verify \
  --halt linux93 \
  -o gen-out/zisk_state_account_inclusion_proof_verify

REPO_ROOT="$(pwd)"

# run_case <name> <mode> [args...]
#
#   present_match    <addr> <nonce> <balance_hex32> <code_mode>
#   present_mismatch <addr> <nonce> <balance_hex32> <code_mode> <bumped_field>
#       bumped_field: nonce | balance | sr | ch
#   absent_match_empty <lookup_addr> <stored_addr>
#   absent_mismatch_eoa <lookup_addr> <stored_addr> <nonce> <balance_hex32>
#   root_not_in_section
run_case() {
  local name="$1"; shift
  local mode="$1"; shift

  local in_file="$REPO_ROOT/gen-out/zisk_saip_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_saip_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_saip_${name}.expected"

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
        return EMPTY_CODE_HASH, EMPTY_TRIE
    if mode.startswith('contract:'):
        code = bytes.fromhex(mode.split(':', 1)[1])
        # contract: storage_root stays as EMPTY_TRIE for simplicity.
        return k256(code), EMPTY_TRIE
    raise SystemExit('bad code_mode: ' + mode)

argv = sys.argv[1:]
mode = '$mode'
parts = [
$(for arg in "$@"; do printf '  %s,\n' "\"$arg\""; done)
]

def build_state_trie(addr, account_rlp):
    path = bytes_to_nibbles(k256(addr))
    leaf = leaf_node(path, account_rlp)
    return k256(leaf), build_ssz_section([leaf])

def pack_struct(nonce, balance, sr, ch):
    # 104-byte struct: nonce u64 LE | balance 32 BE | sr 32 | ch 32.
    balance_be = balance.to_bytes(32, 'big')
    return struct.pack('<Q', nonce) + balance_be + sr + ch

if mode == 'present_match':
    addr = bytes.fromhex(parts[0])
    nonce = int(parts[1])
    balance = int.from_bytes(bytes.fromhex(parts[2]), 'big')
    ch, sr = resolve_code_hash(parts[3])
    acct_rlp = encode_account(nonce, balance, sr, ch)
    state_root, witness_state = build_state_trie(addr, acct_rlp)
    expected_struct = pack_struct(nonce, balance, sr, ch)
    expected = struct.pack('<Q', 0) + struct.pack('<Q', 1)
elif mode == 'present_mismatch':
    addr = bytes.fromhex(parts[0])
    nonce = int(parts[1])
    balance = int.from_bytes(bytes.fromhex(parts[2]), 'big')
    ch, sr = resolve_code_hash(parts[3])
    bumped = parts[4]
    acct_rlp = encode_account(nonce, balance, sr, ch)
    state_root, witness_state = build_state_trie(addr, acct_rlp)
    bumped_nonce, bumped_balance, bumped_sr, bumped_ch = nonce, balance, sr, ch
    if bumped == 'nonce': bumped_nonce ^= 1
    elif bumped == 'balance': bumped_balance ^= 1
    elif bumped == 'sr': bumped_sr = (int.from_bytes(sr, 'big') ^ 1).to_bytes(32, 'big')
    elif bumped == 'ch': bumped_ch = (int.from_bytes(ch, 'big') ^ 1).to_bytes(32, 'big')
    else: raise SystemExit('bad bumped: ' + bumped)
    expected_struct = pack_struct(bumped_nonce, bumped_balance, bumped_sr, bumped_ch)
    expected = struct.pack('<Q', 0) + struct.pack('<Q', 0)
elif mode == 'absent_match_empty':
    addr = bytes.fromhex(parts[0])
    stored_addr = bytes.fromhex(parts[1])
    # Trie contains some other account; addr is absent.
    other_acct = encode_account(7, 1234, EMPTY_TRIE, EMPTY_CODE_HASH)
    state_root, witness_state = build_state_trie(stored_addr, other_acct)
    expected_struct = pack_struct(0, 0, EMPTY_TRIE, EMPTY_CODE_HASH)
    expected = struct.pack('<Q', 1) + struct.pack('<Q', 1)
elif mode == 'absent_mismatch':
    addr = bytes.fromhex(parts[0])
    stored_addr = bytes.fromhex(parts[1])
    nonce = int(parts[2])
    balance = int.from_bytes(bytes.fromhex(parts[3]), 'big')
    other_acct = encode_account(0, 0, EMPTY_TRIE, EMPTY_CODE_HASH)
    state_root, witness_state = build_state_trie(stored_addr, other_acct)
    expected_struct = pack_struct(nonce, balance, EMPTY_TRIE, EMPTY_CODE_HASH)
    expected = struct.pack('<Q', 1) + struct.pack('<Q', 0)
elif mode == 'root_not_in_section':
    addr = bytes.fromhex(parts[0])
    # Caller-supplied state_root not present in witness_state at all.
    state_root = bytes.fromhex('aa' * 32)
    witness_state = build_ssz_section([b'\\xff'])
    # K28 returns 1 (absent) when root miss; is_match=1 iff expected==empty_default.
    expected_struct = pack_struct(0, 0, EMPTY_TRIE, EMPTY_CODE_HASH)
    expected = struct.pack('<Q', 1) + struct.pack('<Q', 1)
else:
    raise SystemExit('bad mode: ' + mode)

with open(argv[0], 'wb') as f:
    record = (
        struct.pack('<Q', len(witness_state))
        + state_root
        + addr
        + expected_struct
        + witness_state
    )
    f.write(record)
    pad = (-len(record)) % 8
    if pad: f.write(b'\\x00' * pad)

with open(argv[1], 'wb') as f:
    f.write(expected)
" "$in_file" "$exp_file"

  "$ZISKEMU" -e gen-out/zisk_state_account_inclusion_proof_verify.elf \
    -i "$in_file" -o "$out_file" -n 4000000 \
    >"$REPO_ROOT/gen-out/zisk_saip_${name}.emu.log" 2>&1 || true

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
ZERO32="$(printf '00%.0s' $(seq 1 32))"

FAILED=0
# 1) EOA present, struct exact match -> status 0, is_match 1.
run_case "present_eoa_match"             present_match "$ALICE" 5 "$(printf '%064x' 1000000000000000000)" "empty" || FAILED=1
# 2) EOA present, expected struct differs in nonce only -> is_match 0.
run_case "present_eoa_mismatch_nonce"    present_mismatch "$ALICE" 5 "$(printf '%064x' 1000000000000000000)" "empty" nonce || FAILED=1
# 3) EOA present, mismatch in code_hash field -> is_match 0.
run_case "present_eoa_mismatch_ch"       present_mismatch "$ALICE" 5 "$(printf '%064x' 1000000000000000000)" "empty" ch || FAILED=1
# 4) Contract present, exact match -> is_match 1.
run_case "present_contract_match"        present_match "$ALICE" 1 "$ZERO32" "contract:600160005500" || FAILED=1
# 5) Contract present, expected differs in storage_root -> is_match 0.
run_case "present_contract_mismatch_sr"  present_mismatch "$ALICE" 1 "$ZERO32" "contract:600160005500" sr || FAILED=1
# 6) Absent account, expected = empty default -> status 1, is_match 1 (spec).
run_case "absent_expect_empty_default"   absent_match_empty "$BOB" "$ALICE" || FAILED=1
# 7) Absent account, expected nonce != 0 -> status 1, is_match 0.
run_case "absent_expect_nonempty"        absent_mismatch "$BOB" "$ALICE" 1 "$ZERO32" || FAILED=1
# 8) Root not in witness section -> status 1 (absent), is_match 1 (vs empty default).
run_case "root_not_in_section"           root_not_in_section "$ALICE" || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: state_account_inclusion_proof_verify end-to-end"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
