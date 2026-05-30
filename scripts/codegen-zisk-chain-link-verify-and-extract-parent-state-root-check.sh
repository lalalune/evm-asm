#!/usr/bin/env bash
# codegen-zisk-chain-link-verify-and-extract-parent-state-root-check.sh
#
# One-call composite: verify chain link AND extract parent's
# state_root. Sibling of #7222 with the extracted root
# included in the output.
#
# Output (48 bytes):
#   bytes  0.. 8 : status (0..4)
#   bytes  8..16 : is_valid (u64; 0 or 1)
#   bytes 16..48 : parent_state_root (32 B)
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

echo "==> emit zisk_chain_link_verify_and_extract_parent_state_root ELF"
lake exe codegen --program zisk_chain_link_verify_and_extract_parent_state_root \
  --halt linux93 \
  -o gen-out/zisk_chain_link_verify_and_extract_parent_state_root

REPO_ROOT="$(pwd)"

run_case() {
  local name="$1"; shift
  local mode="$1"; shift

  local in_file="$REPO_ROOT/gen-out/zisk_clve_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_clve_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_clve_${name}.expected"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys
import rlp
from Crypto.Hash import keccak

def k256(b):
    h = keccak.new(digest_bits=256); h.update(b); return h.digest()

def encode_header(parent_hash, state_root):
    fields = [
        parent_hash, b'\\x22'*32, b'\\x33'*20, state_root, b'\\x55'*32,
        b'\\x66'*32, b'\\x00'*256, b'', b'\\x01', b'\\x83\\xff\\xff\\xff',
        b'', b'\\x83\\x01\\x02\\x03', b'', b'\\x77'*32, b'\\x00'*8,
    ]
    return rlp.encode(fields)

mode = '$mode'
PARENT_SR = b'\\x44' * 32
CHILD_SR = b'\\x55' * 32

if mode == 'valid_link_with_extract':
    parent_rlp = encode_header(b'\\xab'*32, PARENT_SR)
    parent_keccak = k256(parent_rlp)
    child_rlp = encode_header(parent_keccak, CHILD_SR)
    expected = (
        struct.pack('<Q', 0)
        + struct.pack('<Q', 1)
        + PARENT_SR
    )
elif mode == 'invalid_link_root_still_extracted':
    # Link mismatched; primitive still extracts parent.state_root.
    parent_rlp = encode_header(b'\\xab'*32, PARENT_SR)
    other_keccak = b'\\xee'*32
    child_rlp = encode_header(other_keccak, CHILD_SR)
    expected = (
        struct.pack('<Q', 0)
        + struct.pack('<Q', 0)
        + PARENT_SR
    )
elif mode == 'child_parse_fail':
    parent_rlp = encode_header(b'\\xab'*32, PARENT_SR)
    child_rlp = b'\\x00'
    expected = (
        struct.pack('<Q', 1)
        + struct.pack('<Q', 0)
        + b'\\x00' * 32
    )
elif mode == 'parent_parse_fail':
    # Child is valid; but parent header is too short to parse.
    # is_valid will be 0 (keccak of garbage will not match any
    # claimed parent_hash here).
    parent_rlp = b'\\x00'
    # Construct a child whose parent_hash happens to equal keccak(b'\\x00').
    parent_keccak = k256(parent_rlp)
    child_rlp = encode_header(parent_keccak, CHILD_SR)
    # Link IS valid (we crafted parent_hash that way),
    # but parent state_root extraction fails. Status -> 3.
    expected = (
        struct.pack('<Q', 3)
        + struct.pack('<Q', 1)
        + b'\\x00' * 32  # state_root was pre-zeroed at start
    )
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

  "$ZISKEMU" -e gen-out/zisk_chain_link_verify_and_extract_parent_state_root.elf \
    -i "$in_file" -o "$out_file" -n 4000000 \
    >"$REPO_ROOT/gen-out/zisk_clve_${name}.emu.log" 2>&1 || true

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
run_case "valid_link_with_extract"          valid_link_with_extract || FAILED=1
run_case "invalid_link_root_extracted"      invalid_link_root_still_extracted || FAILED=1
run_case "child_parse_fail"                 child_parse_fail || FAILED=1
run_case "parent_parse_fail_link_valid"     parent_parse_fail || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: chain_link_verify_and_extract_parent_state_root end-to-end"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
