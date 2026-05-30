#!/usr/bin/env bash
# codegen-zisk-state-root-present-in-witness-state-check.sh
#
# Pure presence predicate: K19 over witness.state with a
# caller-supplied state_root. Symmetric to #7204 for the
# storage side.
#
# Output (16 bytes):
#   bytes  0.. 8 : status (always 0)
#   bytes  8..16 : is_present (u64; 0 or 1)
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

echo "==> emit zisk_state_root_present_in_witness_state ELF"
lake exe codegen --program zisk_state_root_present_in_witness_state \
  --halt linux93 \
  -o gen-out/zisk_state_root_present_in_witness_state

REPO_ROOT="$(pwd)"

run_case() {
  local name="$1"; shift
  local mode="$1"; shift

  local in_file="$REPO_ROOT/gen-out/zisk_srpws_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_srpws_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_srpws_${name}.expected"

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

mode = '$mode'

if mode == 'single_leaf':
    leaf = leaf_node(bytes_to_nibbles(b'\\xaa'*32), b'value-A')
    state_root = k256(leaf)
    witness_state = build_ssz_section([leaf])
    expected = struct.pack('<Q', 0) + struct.pack('<Q', 1)
elif mode == 'multi_with_target':
    decoy1 = leaf_node(bytes_to_nibbles(b'\\xcc'*32), b'decoy-1')
    leaf   = leaf_node(bytes_to_nibbles(b'\\xaa'*32), b'value-A')
    decoy2 = leaf_node(bytes_to_nibbles(b'\\xdd'*32), b'decoy-2')
    state_root = k256(leaf)
    witness_state = build_ssz_section([decoy1, leaf, decoy2])
    expected = struct.pack('<Q', 0) + struct.pack('<Q', 1)
elif mode == 'empty_section':
    leaf = leaf_node(bytes_to_nibbles(b'\\xaa'*32), b'value-A')
    state_root = k256(leaf)
    witness_state = b''
    expected = struct.pack('<Q', 0) + struct.pack('<Q', 0)
elif mode == 'unrelated_nodes':
    leaf = leaf_node(bytes_to_nibbles(b'\\xaa'*32), b'value-A')
    state_root = k256(leaf)
    decoy1 = leaf_node(bytes_to_nibbles(b'\\xcc'*32), b'decoy-1')
    decoy2 = leaf_node(bytes_to_nibbles(b'\\xdd'*32), b'decoy-2')
    witness_state = build_ssz_section([decoy1, decoy2])
    expected = struct.pack('<Q', 0) + struct.pack('<Q', 0)
elif mode == 'zero_root':
    state_root = b'\\x00' * 32
    decoy = leaf_node(bytes_to_nibbles(b'\\xcc'*32), b'decoy')
    witness_state = build_ssz_section([decoy])
    expected = struct.pack('<Q', 0) + struct.pack('<Q', 0)
else:
    raise SystemExit('bad mode')

with open(sys.argv[1], 'wb') as f:
    record = (
        struct.pack('<Q', len(witness_state))
        + state_root
        + witness_state
    )
    f.write(record)
    pad = (-len(record)) % 8
    if pad: f.write(b'\\x00' * pad)

with open(sys.argv[2], 'wb') as f:
    f.write(expected)
" "$in_file" "$exp_file"

  "$ZISKEMU" -e gen-out/zisk_state_root_present_in_witness_state.elf \
    -i "$in_file" -o "$out_file" -n 4000000 \
    >"$REPO_ROOT/gen-out/zisk_srpws_${name}.emu.log" 2>&1 || true

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
run_case "root_is_single_leaf"             single_leaf || FAILED=1
run_case "root_in_multi_entry"             multi_with_target || FAILED=1
run_case "empty_section"                   empty_section || FAILED=1
run_case "unrelated_nodes_only"            unrelated_nodes || FAILED=1
run_case "zero_root_lookup_absent"         zero_root || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: state_root_present_in_witness_state end-to-end"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
