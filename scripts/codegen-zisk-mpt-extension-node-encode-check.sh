#!/usr/bin/env bash
# codegen-zisk-mpt-extension-node-encode-check.sh -- PR-K164.
#
# Encode an MPT extension node:
#   ext_node = rlp([hp_encode_nibbles(shared_path, is_leaf=false),
#                   child_ref_bytes])
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

echo "==> emit zisk_mpt_extension_node_encode ELF"
lake exe codegen --program zisk_mpt_extension_node_encode --halt linux93 \
  -o gen-out/zisk_mpt_extension_node_encode

REPO_ROOT="$(pwd)"

# run_case <name> <path_nibbles_hex> <child_ref_hex>
# path_nibbles_hex is a hex string where each byte represents one nibble
# (low 4 bits). E.g., "0806" means nibbles [0, 8, 0, 6] → path "0806" packed.
# child_ref_hex is the parent-slot encoding (output of K163), already a
# valid RLP item.
run_case() {
  local name="$1" path_nibs="$2" child="$3"

  local in_file="$REPO_ROOT/gen-out/zisk_mpt_extension_node_encode_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_mpt_extension_node_encode_${name}.output"
  local exp_hex_file="$REPO_ROOT/gen-out/zisk_mpt_extension_node_encode_${name}.expected.hex"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys, rlp
nibbles_bytes = bytes.fromhex('$path_nibs')
nibbles = list(nibbles_bytes)  # each byte is one nibble (low 4 bits)
child = bytes.fromhex('$child')

# HP-encode with is_leaf=False.
flag = 0 + (len(nibbles) & 1)
hp = bytearray()
if len(nibbles) % 2 == 1:
    hp.append((flag << 4) | nibbles[0])
    i = 1
else:
    hp.append(flag << 4)
    i = 0
while i < len(nibbles):
    hp.append((nibbles[i] << 4) | nibbles[i+1])
    i += 2

# Build inner payload = rlp(hp) || child_bytes
hp_rlp = rlp.encode(bytes(hp))
payload = hp_rlp + child

# Outer list prefix
n = len(payload)
if n < 56:
    prefix = bytes([0xc0 + n])
else:
    n_bytes = n.to_bytes((n.bit_length() + 7) // 8, 'big')
    prefix = bytes([0xf7 + len(n_bytes)]) + n_bytes
ext_node_rlp = prefix + payload

with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(nibbles)))
    f.write(struct.pack('<Q', len(child)))
    f.write(bytes(nibbles))
    f.write(child)
    pad = (-(16 + len(nibbles) + len(child))) % 8
    if pad: f.write(b'\x00' * pad)
with open(sys.argv[2], 'w') as f:
    f.write(ext_node_rlp.hex())
" "$in_file" "$exp_hex_file"

  "$ZISKEMU" -e gen-out/zisk_mpt_extension_node_encode.elf \
    -i "$in_file" -o "$out_file" -n 1000000 \
    >"$REPO_ROOT/gen-out/zisk_mpt_extension_node_encode_${name}.emu.log" 2>&1 || true

  local actual_status; actual_status="$(xxd -p -l 8 "$out_file" | tr -d '\n')"
  local actual_len_le; actual_len_le="$(dd if="$out_file" bs=1 skip=8 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local actual_len; actual_len="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$actual_len_le'))[0])")"
  local expected_hex; expected_hex="$(cat "$exp_hex_file")"
  local expected_len; expected_len=$(( ${#expected_hex} / 2 ))
  local cmp_len=$expected_len
  if [[ $cmp_len -gt 240 ]]; then cmp_len=240; fi
  local actual_hex; actual_hex="$(dd if="$out_file" bs=1 skip=16 count="$cmp_len" 2>/dev/null | xxd -p | tr -d '\n')"
  local expected_prefix="${expected_hex:0:$((2 * cmp_len))}"

  if [[ "$actual_status" == "0000000000000000" \
       && "$actual_len" == "$expected_len" \
       && "$actual_hex" == "$expected_prefix" ]]; then
    printf "  %-30s OK   len=%d\n" "$name" "$expected_len"
    return 0
  else
    printf "  %-30s FAIL status=0x%s actual_len=%d expected_len=%d\n" "$name" "$actual_status" "$actual_len" "$expected_len"
    printf "      actual:   %s...\n" "${actual_hex:0:80}"
    printf "      expected: %s...\n" "${expected_prefix:0:80}"
    return 1
  fi
}

# Helper to build child_ref bytes: keccak256(node_rlp) wrapped with 0xa0
# (for the typical hashed case). Hardcoded sample 32B hash:
HASH32="a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0"
HASHED_CHILD="a0$HASH32"

# Short inline child (e.g., a small leaf node serialized directly):
SHORT_CHILD="c4820080"

FAILED=0
# Even-count nibbles (e.g., [0, 8]) with hashed child
run_case "even_nibbles_hashed"   "0008" "$HASHED_CHILD" || FAILED=1
# Odd-count nibbles (e.g., [8]) with hashed child
run_case "odd_nibbles_hashed"    "08"   "$HASHED_CHILD" || FAILED=1
# Long even path
run_case "long_even_path_hashed" "0102030405060708" "$HASHED_CHILD" || FAILED=1
# Short inline child (rare in practice)
run_case "short_inline_child"    "0008" "$SHORT_CHILD"  || FAILED=1
# Single nibble
run_case "single_nibble"         "0c"   "$HASHED_CHILD" || FAILED=1
# 32 nibbles (typical state-trie depth)
run_case "32_nibble_path"        "$(python3 -c "print('0a' * 32)")" "$HASHED_CHILD" || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: mpt_extension_node_encode matches Python rlp + HP-encode (is_leaf=false)"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
