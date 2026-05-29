#!/usr/bin/env bash
# codegen-zisk-storage-root-recompute-single-slot-check.sh
#
# Recompute the storage trie root for a single-slot trie:
#   key = keccak256(slot_idx_BE)
#   value = rlp.encode(slot_value)
#   leaf = rlp.encode([hp_encode(nibbles(key), is_leaf=True), value])
#   storage_root = keccak256(leaf)
#
# Output (40 bytes):
#   bytes  0.. 8 : status (always 0)
#   bytes  8..40 : storage_root (32 bytes)
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

echo "==> emit zisk_storage_root_recompute_single_slot ELF"
lake exe codegen --program zisk_storage_root_recompute_single_slot \
  --halt linux93 \
  -o gen-out/zisk_storage_root_recompute_single_slot

REPO_ROOT="$(pwd)"

# run_case <name> <slot_idx_hex_64> <slot_value_dec>
run_case() {
  local name="$1" slot_idx="$2" slot_value="$3"

  local in_file="$REPO_ROOT/gen-out/zisk_srss_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_srss_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_srss_${name}.expected"

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

def bytes_to_nibbles(b):
    out = []
    for byte in b:
        out.append(byte >> 4)
        out.append(byte & 0xf)
    return out

slot_idx = bytes.fromhex('$slot_idx')
slot_value = int('$slot_value')
slot_value_be = slot_value.to_bytes(32, 'big')

# MPT key for storage = keccak256(slot_idx_BE)
hashed_key = k256(slot_idx)
path = bytes_to_nibbles(hashed_key)
hp = hp_encode(path, is_leaf=True)
# Value = rlp.encode(slot_value)
value_rlp = rlp.encode(slot_value)
# Leaf = rlp.encode([hp, value_rlp])
leaf = rlp.encode([hp, value_rlp])
storage_root = k256(leaf)

expected = struct.pack('<Q', 0) + storage_root

with open(sys.argv[1], 'wb') as f:
    f.write(slot_idx + slot_value_be)

with open(sys.argv[2], 'wb') as f:
    f.write(expected)
" "$in_file" "$exp_file"

  "$ZISKEMU" -e gen-out/zisk_storage_root_recompute_single_slot.elf \
    -i "$in_file" -o "$out_file" -n 2000000 \
    >"$REPO_ROOT/gen-out/zisk_srss_${name}.emu.log" 2>&1 || true

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

FAILED=0
# Slot 0 with various values.
run_case "slot0_value0"   "0000000000000000000000000000000000000000000000000000000000000000" 0 || FAILED=1
run_case "slot0_value1"   "0000000000000000000000000000000000000000000000000000000000000000" 1 || FAILED=1
run_case "slot0_value127" "0000000000000000000000000000000000000000000000000000000000000000" 127 || FAILED=1
run_case "slot0_value128" "0000000000000000000000000000000000000000000000000000000000000000" 128 || FAILED=1
run_case "slot0_value1e18" "0000000000000000000000000000000000000000000000000000000000000000" 1000000000000000000 || FAILED=1
run_case "slot0_max_u256" "0000000000000000000000000000000000000000000000000000000000000000" 115792089237316195423570985008687907853269984665640564039457584007913129639935 || FAILED=1
# Different slot indices.
run_case "slot1_value42"  "0000000000000000000000000000000000000000000000000000000000000001" 42 || FAILED=1
run_case "slot_keccak_keyed" "abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789" 100 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: storage_root_recompute_single_slot end-to-end"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
