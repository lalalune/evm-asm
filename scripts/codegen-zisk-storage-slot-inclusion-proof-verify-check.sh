#!/usr/bin/env bash
# codegen-zisk-storage-slot-inclusion-proof-verify-check.sh
#
# Light-client storage-inclusion-proof primitive. Distinct from
# verify_slot_value_matches (PR #7188): takes a trusted
# storage_root DIRECTLY rather than walking a header's state
# trie to derive one.
#
# Spec-distinguishing rows:
#
#   | slot in trie? | stored val | expected | status | is_match |
#   |---------------|------------|----------|--------|----------|
#   | yes           | V          | V        |   0    |    1     |
#   | yes           | V          | V'       |   0    |    0     |
#   | no            | 0 (SLOAD)  | 0        |   1    |    1     |
#   | no            | 0 (SLOAD)  | nonzero  |   1    |    0     |
#   | mpt parse fail|     -      |    -     |   2    |    0     |
#
# Output (16 bytes):
#   bytes  0.. 8 : status (0=ok / 1=slot-absent / 2=parse fail / 3=slot RLP fail)
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

echo "==> emit zisk_storage_slot_inclusion_proof_verify ELF"
lake exe codegen --program zisk_storage_slot_inclusion_proof_verify \
  --halt linux93 \
  -o gen-out/zisk_storage_slot_inclusion_proof_verify

REPO_ROOT="$(pwd)"

# run_case <name> <mode> [args...]
#
#   present <slot_idx_hex32_BE> <stored_value_hex32_BE> <expected_hex32_BE>
#   missing <lookup_idx_hex32_BE> <stored_idx_hex32_BE> <stored_value_hex32_BE> <expected_hex32_BE>
#   root_not_in_section  (storage_root not present anywhere in witness.storage)
run_case() {
  local name="$1"; shift
  local mode="$1"; shift

  local in_file="$REPO_ROOT/gen-out/zisk_ssip_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_ssip_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_ssip_${name}.expected"

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

def storage_trie_one_slot(slot_idx_be, value_be):
    # Spec leaf: key = keccak(slot_idx_be), value = RLP(big-endian-min-encoding(value)).
    path = bytes_to_nibbles(k256(slot_idx_be))
    v = value_be.lstrip(b'\\x00')
    if v == b'':
        v = b''
    leaf = leaf_node(path, rlp.encode(v))
    return k256(leaf), build_ssz_section([leaf])

argv = sys.argv[1:]
mode = '$mode'
parts = [
$(for arg in "$@"; do printf '  %s,\n' "\"$arg\""; done)
]

if mode == 'present':
    slot_idx_be   = bytes.fromhex(parts[0])
    stored_be     = bytes.fromhex(parts[1])
    expected_be   = bytes.fromhex(parts[2])
    storage_root, witness_storage = storage_trie_one_slot(slot_idx_be, stored_be)
    is_match = 1 if stored_be == expected_be else 0
    expected = struct.pack('<Q', 0) + struct.pack('<Q', is_match)
elif mode == 'missing':
    lookup_idx_be = bytes.fromhex(parts[0])
    stored_idx_be = bytes.fromhex(parts[1])
    stored_be     = bytes.fromhex(parts[2])
    expected_be   = bytes.fromhex(parts[3])
    storage_root, witness_storage = storage_trie_one_slot(stored_idx_be, stored_be)
    slot_idx_be = lookup_idx_be
    # On slot-absent, SLOAD yields 0 -- match iff expected is zero.
    is_match = 1 if expected_be == b'\\x00'*32 else 0
    expected = struct.pack('<Q', 1) + struct.pack('<Q', is_match)
elif mode == 'root_not_in_section':
    # Root absent from witness.storage = slot trivially missing
    # from the trie. Per K29 contract this surfaces as status 1
    # (slot-missing). The SLOAD spec then implies value 0, so
    # is_match = 1 iff the caller-supplied expected is also 0.
    slot_idx_be   = bytes.fromhex(parts[0])
    expected_be   = bytes.fromhex(parts[1])
    storage_root  = bytes.fromhex(parts[2])  # not present in section
    witness_storage = build_ssz_section([b'\\xff'])
    is_match = 1 if expected_be == b'\\x00'*32 else 0
    expected = struct.pack('<Q', 1) + struct.pack('<Q', is_match)
else:
    raise SystemExit('bad mode: ' + mode)

with open(argv[0], 'wb') as f:
    record = (
        struct.pack('<Q', len(witness_storage))
        + storage_root
        + slot_idx_be
        + expected_be
        + witness_storage
    )
    f.write(record)
    pad = (-len(record)) % 8
    if pad: f.write(b'\\x00' * pad)

with open(argv[1], 'wb') as f:
    f.write(expected)
" "$in_file" "$exp_file"

  "$ZISKEMU" -e gen-out/zisk_storage_slot_inclusion_proof_verify.elf \
    -i "$in_file" -o "$out_file" -n 4000000 \
    >"$REPO_ROOT/gen-out/zisk_ssip_${name}.emu.log" 2>&1 || true

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

# 32-byte BE u256 helpers.
hex32() { printf '%064x' "$1"; }

ZERO32="$(printf '00%.0s' $(seq 1 32))"

# Slot indices and values (32-byte BE u256).
SLOT0="$(hex32 0)"
SLOT1="$(hex32 1)"
SLOT_FF="$(printf 'ff%.0s' $(seq 1 32))"

VAL_42="$(hex32 0x42)"
VAL_43="$(hex32 0x43)"
VAL_DEADBEEF="$(hex32 0xdeadbeef)"

GARBAGE_ROOT="$(printf 'aa%.0s' $(seq 1 32))"

FAILED=0

# 1) Present + match: stored=0x42, expected=0x42 -> status 0, is_match 1.
run_case "present_match_small"             present "$SLOT0" "$VAL_42" "$VAL_42" || FAILED=1
# 2) Present + mismatch: stored=0x42, expected=0x43 -> status 0, is_match 0.
run_case "present_mismatch_small"          present "$SLOT0" "$VAL_42" "$VAL_43" || FAILED=1
# 3) Present + match on a different slot index (uses keccak path).
run_case "present_match_slot_ff"           present "$SLOT_FF" "$VAL_DEADBEEF" "$VAL_DEADBEEF" || FAILED=1
# 4) Absent slot, expected 0 -> status 1 (slot-missing), is_match 1 (SLOAD-zero semantics).
run_case "absent_expect_zero_sload_zero"   missing "$SLOT0" "$SLOT1" "$VAL_42" "$ZERO32" || FAILED=1
# 5) Absent slot, expected nonzero -> status 1, is_match 0.
run_case "absent_expect_nonzero_no_match"  missing "$SLOT0" "$SLOT1" "$VAL_42" "$VAL_42" || FAILED=1
# 6) Root not in witness.storage section: per K29, surfaces as
#    status 1 (slot-missing). With expected != 0, is_match = 0.
run_case "root_not_in_section_nonzero_exp" root_not_in_section "$SLOT0" "$VAL_42" "$GARBAGE_ROOT" || FAILED=1
# 7) Root not in witness.storage, expected zero -> status 1, is_match 1.
run_case "root_not_in_section_zero_exp"    root_not_in_section "$SLOT0" "$ZERO32" "$GARBAGE_ROOT" || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: storage_slot_inclusion_proof_verify end-to-end"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
