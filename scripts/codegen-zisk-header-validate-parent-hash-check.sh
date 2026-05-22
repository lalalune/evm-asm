#!/usr/bin/env bash
# codegen-zisk-header-validate-parent-hash-check.sh -- PR-K94.
#
# Verify header.parent_hash == keccak256(rlp.encode(parent_header)).
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

echo "==> emit zisk_header_validate_parent_hash ELF"
lake exe codegen --program zisk_header_validate_parent_hash --halt linux93 \
  -o gen-out/zisk_header_validate_parent_hash

REPO_ROOT="$(pwd)"

# run_case <name> <use_correct_parent_hash> <expected_status>
# use_correct_parent_hash: "match" | "wrong" | "junk"
run_case() {
  local name="$1" mode="$2" exp="$3"

  local in_file="$REPO_ROOT/gen-out/zisk_header_validate_parent_hash_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_header_validate_parent_hash_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys, rlp
from Crypto.Hash import keccak

def make_header(parent_hash_bytes):
    return [
        parent_hash_bytes, bytes(32), bytes(20), bytes(32), bytes(32),
        bytes(32), bytes(256), 0, 1, 30_000_000,
        100_000, 1700000000, b'', bytes(32), bytes(8),
        10**9, bytes(32), 0, 0,
        bytes(32), bytes(32), bytes(32),
    ]

parent = make_header(bytes([0xaa]*32))
parent_rlp = rlp.encode(parent)
real_phash = keccak.new(digest_bits=256).update(parent_rlp).digest()

mode = '$mode'
if mode == 'match':
    phash = real_phash
elif mode == 'wrong':
    phash = bytes([0x55]*32)
elif mode == 'junk':
    phash = bytes([0xff]*32)
else:
    raise ValueError(mode)

this = make_header(phash)
this_rlp = rlp.encode(this)

with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(this_rlp)))
    f.write(struct.pack('<Q', len(parent_rlp)))
    f.write(this_rlp)
    f.write(parent_rlp)
    total = 16 + len(this_rlp) + len(parent_rlp)
    pad = (-total) % 8
    if pad: f.write(b'\x00' * pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_header_validate_parent_hash.elf \
    -i "$in_file" -o "$out_file" -n 5000000 \
    >"$REPO_ROOT/gen-out/zisk_header_validate_parent_hash_${name}.emu.log" 2>&1 || true

  local actual_status; actual_status="$(xxd -p -l 8 "$out_file" | tr -d '\n')"
  local exp_status_le; exp_status_le="$(python3 -c "print(int('$exp').to_bytes(8, 'little').hex())")"

  if [[ "$actual_status" == "$exp_status_le" ]]; then
    printf "  %-32s OK   status=%d\n" "$name" "$exp"
    return 0
  else
    printf "  %-32s FAIL status=0x%s expected=%d\n" "$name" "$actual_status" "$exp"
    return 1
  fi
}

FAILED=0
run_case "match"              match  0 || FAILED=1
run_case "wrong_phash"        wrong  2 || FAILED=1
run_case "junk_phash"         junk   2 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: header_validate_parent_hash matches header.parent_hash to keccak256(parent_rlp)"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
