#!/usr/bin/env bash
# codegen-zisk-header-chain-walk-step-check.sh -- PR-K96.
#
# One-step chain validation: verify child.parent_hash == prev_hash,
# then compute keccak256(child_rlp).
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

echo "==> emit zisk_header_chain_walk_step ELF"
lake exe codegen --program zisk_header_chain_walk_step --halt linux93 \
  -o gen-out/zisk_header_chain_walk_step

REPO_ROOT="$(pwd)"

# run_case <name> <use_correct_prev> <expected_status>
# use_correct_prev: "match" | "wrong"
run_case() {
  local name="$1" mode="$2" exp="$3"

  local in_file="$REPO_ROOT/gen-out/zisk_header_chain_walk_step_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_header_chain_walk_step_${name}.output"

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
real_parent_hash = keccak.new(digest_bits=256).update(parent_rlp).digest()

child = make_header(real_parent_hash)
child_rlp = rlp.encode(child)
real_child_hash = keccak.new(digest_bits=256).update(child_rlp).digest()

mode = '$mode'
if mode == 'match':
    prev = real_parent_hash
elif mode == 'wrong':
    prev = bytes([0x55]*32)
else:
    raise ValueError(mode)

with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(child_rlp)))
    f.write(prev.ljust(32, b'\x00'))
    f.write(child_rlp)
    total = 8 + 32 + len(child_rlp)
    pad = (-total) % 8
    if pad: f.write(b'\x00' * pad)

with open(sys.argv[1] + '.expected_hash', 'wb') as f:
    f.write(real_child_hash)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_header_chain_walk_step.elf \
    -i "$in_file" -o "$out_file" -n 5000000 \
    >"$REPO_ROOT/gen-out/zisk_header_chain_walk_step_${name}.emu.log" 2>&1 || true

  local actual_status; actual_status="$(xxd -p -l 8 "$out_file" | tr -d '\n')"
  local exp_status_le; exp_status_le="$(python3 -c "print(int('$exp').to_bytes(8, 'little').hex())")"

  if [[ "$exp" == "0" ]]; then
    local actual_hash; actual_hash="$(dd if="$out_file" bs=1 skip=8 count=32 2>/dev/null | xxd -p | tr -d '\n')"
    local exp_hash; exp_hash="$(xxd -p "$in_file.expected_hash" | tr -d '\n')"
    if [[ "$actual_status" == "$exp_status_le" && "$actual_hash" == "$exp_hash" ]]; then
      printf "  %-32s OK   match → hash %s..\n" "$name" "${actual_hash:0:16}"
      return 0
    else
      printf "  %-32s FAIL status=0x%s hash=0x%s\n" "$name" "$actual_status" "${actual_hash:0:16}"
      return 1
    fi
  else
    if [[ "$actual_status" == "$exp_status_le" ]]; then
      printf "  %-32s OK   status=%d (rejected)\n" "$name" "$exp"
      return 0
    else
      printf "  %-32s FAIL status=0x%s expected=%d\n" "$name" "$actual_status" "$exp"
      return 1
    fi
  fi
}

FAILED=0
run_case "match"              match  0 || FAILED=1
run_case "wrong_prev"         wrong  2 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: header_chain_walk_step verifies parent_hash and computes child hash"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
