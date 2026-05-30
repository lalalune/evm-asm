#!/usr/bin/env bash
# codegen-zisk-parent-keccak-matches-child-parent-hash-check.sh
#
# Multi-block chain-link hash consistency: keccak(parent_rlp)
# vs child.parent_hash. The fundamental hash-based chain
# check.
#
# Output (16 bytes):
#   bytes  0.. 8 : status (0/1/2)
#   bytes  8..16 : is_valid (u64; 0 or 1)
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

echo "==> emit zisk_parent_keccak_matches_child_parent_hash ELF"
lake exe codegen --program zisk_parent_keccak_matches_child_parent_hash \
  --halt linux93 \
  -o gen-out/zisk_parent_keccak_matches_child_parent_hash

REPO_ROOT="$(pwd)"

run_case() {
  local name="$1"; shift
  local mode="$1"; shift

  local in_file="$REPO_ROOT/gen-out/zisk_pkmc_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_pkmc_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_pkmc_${name}.expected"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys
import rlp
from Crypto.Hash import keccak

def k256(b):
    h = keccak.new(digest_bits=256); h.update(b); return h.digest()

def encode_header(parent_hash, state_root=None):
    if state_root is None:
        state_root = b'\\x44'*32
    fields = [
        parent_hash, b'\\x22'*32, b'\\x33'*20, state_root, b'\\x55'*32,
        b'\\x66'*32, b'\\x00'*256, b'', b'\\x01', b'\\x83\\xff\\xff\\xff',
        b'', b'\\x83\\x01\\x02\\x03', b'', b'\\x77'*32, b'\\x00'*8,
    ]
    return rlp.encode(fields)

mode = '$mode'

if mode == 'valid_link':
    parent_rlp = encode_header(b'\\xab'*32, state_root=b'\\x44'*32)
    parent_keccak = k256(parent_rlp)
    child_rlp = encode_header(parent_keccak, state_root=b'\\x55'*32)
    expected = struct.pack('<Q', 0) + struct.pack('<Q', 1)
elif mode == 'wrong_parent':
    # child's parent_hash points to a different parent.
    parent_rlp = encode_header(b'\\xab'*32, state_root=b'\\x44'*32)
    other_keccak = b'\\xee'*32
    child_rlp = encode_header(other_keccak, state_root=b'\\x55'*32)
    expected = struct.pack('<Q', 0) + struct.pack('<Q', 0)
elif mode == 'parent_byte_modified':
    # Same shape as valid_link, but modify one byte of parent_rlp
    # so its keccak no longer matches child.parent_hash.
    parent_rlp_orig = encode_header(b'\\xab'*32, state_root=b'\\x44'*32)
    parent_keccak = k256(parent_rlp_orig)
    parent_rlp_corrupted = parent_rlp_orig[:-1] + bytes([parent_rlp_orig[-1] ^ 0x01])
    child_rlp = encode_header(parent_keccak, state_root=b'\\x55'*32)
    parent_rlp = parent_rlp_corrupted
    expected = struct.pack('<Q', 0) + struct.pack('<Q', 0)
elif mode == 'child_parse_fail':
    parent_rlp = encode_header(b'\\xab'*32)
    child_rlp = b'\\x00'  # too small to parse 15-field list
    expected = struct.pack('<Q', 1) + struct.pack('<Q', 0)
else:
    raise SystemExit('bad mode: ' + mode)

with open(sys.argv[1], 'wb') as f:
    record = (
        struct.pack('<Q', len(parent_rlp))
        + struct.pack('<Q', len(child_rlp))
        + parent_rlp
        + child_rlp
    )
    f.write(record)
    pad = (-len(record)) % 8
    if pad: f.write(b'\\x00' * pad)

with open(sys.argv[2], 'wb') as f:
    f.write(expected)
" "$in_file" "$exp_file"

  "$ZISKEMU" -e gen-out/zisk_parent_keccak_matches_child_parent_hash.elf \
    -i "$in_file" -o "$out_file" -n 4000000 \
    >"$REPO_ROOT/gen-out/zisk_pkmc_${name}.emu.log" 2>&1 || true

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

FAILED=0
# 1) Valid chain link.
run_case "valid_link"               valid_link || FAILED=1
# 2) Wrong parent (different parent altogether).
run_case "wrong_parent_hash"        wrong_parent || FAILED=1
# 3) Parent bytes modified by 1 -> keccak differs -> mismatch.
run_case "parent_byte_modified"     parent_byte_modified || FAILED=1
# 4) Child header bytes too short to parse -> status 1.
run_case "child_parse_fail"         child_parse_fail || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: parent_keccak_matches_child_parent_hash end-to-end"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
