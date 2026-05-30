#!/usr/bin/env bash
# codegen-zisk-parent-state-root-present-in-witness-state-check.sh
#
# Precondition primitive for state-trie verification:
# extract header.state_root from a parent_header_rlp and
# check whether witness.state contains a node whose
# keccak256 equals that state_root. Does NOT walk -- just
# screening for reachability.
#
# Distinguishing fixtures:
#
#   | witness.state has node with hash == state_root? | status | is_present |
#   |--------------------------------------------------|--------|------------|
#   | yes (state_root is the single leaf)              |   0    |     1      |
#   | yes (multi-entry section, root somewhere)        |   0    |     1      |
#   | no (empty section)                               |   0    |     0      |
#   | no (other nodes only)                            |   0    |     0      |
#   | header parse fails                               |   1    |     0      |
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

echo "==> emit zisk_parent_state_root_present_in_witness_state ELF"
lake exe codegen --program zisk_parent_state_root_present_in_witness_state \
  --halt linux93 \
  -o gen-out/zisk_parent_state_root_present_in_witness_state

REPO_ROOT="$(pwd)"

# run_case <name> <mode>
#
#   mode: single_leaf | multi_entry_with_root | empty_state |
#         other_nodes_only | garbage_header
run_case() {
  local name="$1"; shift
  local mode="$1"; shift

  local in_file="$REPO_ROOT/gen-out/zisk_psrp_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_psrp_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_psrp_${name}.expected"

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

def encode_header(state_root):
    fields = [
        b'\\x11'*32, b'\\x22'*32, b'\\x33'*20, state_root, b'\\x55'*32,
        b'\\x66'*32, b'\\x00'*256, b'', b'\\x01', b'\\x83\\xff\\xff\\xff',
        b'', b'\\x83\\x01\\x02\\x03', b'', b'\\x77'*32, b'\\x00'*8,
    ]
    return rlp.encode(fields)

mode = '$mode'

if mode == 'single_leaf':
    leaf = leaf_node(bytes_to_nibbles(b'\\xaa'*32), b'value-A')
    state_root = k256(leaf)
    witness_state = build_ssz_section([leaf])
    header = encode_header(state_root)
    expected = struct.pack('<Q', 0) + struct.pack('<Q', 1)
elif mode == 'multi_entry_with_root':
    decoy1 = leaf_node(bytes_to_nibbles(b'\\xcc'*32), b'decoy-1')
    leaf = leaf_node(bytes_to_nibbles(b'\\xaa'*32), b'value-A')
    decoy2 = leaf_node(bytes_to_nibbles(b'\\xdd'*32), b'decoy-2')
    state_root = k256(leaf)
    witness_state = build_ssz_section([decoy1, leaf, decoy2])
    header = encode_header(state_root)
    expected = struct.pack('<Q', 0) + struct.pack('<Q', 1)
elif mode == 'empty_state':
    leaf = leaf_node(bytes_to_nibbles(b'\\xaa'*32), b'value-A')
    state_root = k256(leaf)
    witness_state = b''
    header = encode_header(state_root)
    expected = struct.pack('<Q', 0) + struct.pack('<Q', 0)
elif mode == 'other_nodes_only':
    leaf = leaf_node(bytes_to_nibbles(b'\\xaa'*32), b'value-A')
    state_root_referenced = k256(leaf)
    # Witness contains different nodes whose hashes don't match.
    decoy1 = leaf_node(bytes_to_nibbles(b'\\xcc'*32), b'decoy-1')
    decoy2 = leaf_node(bytes_to_nibbles(b'\\xdd'*32), b'decoy-2')
    witness_state = build_ssz_section([decoy1, decoy2])
    header = encode_header(state_root_referenced)
    expected = struct.pack('<Q', 0) + struct.pack('<Q', 0)
elif mode == 'garbage_header':
    state_root = b'\\xee' * 32
    witness_state = b''
    header = b'\\x00'  # too small to parse a 15-field list
    expected = struct.pack('<Q', 1) + struct.pack('<Q', 0)
else:
    raise SystemExit('bad mode: ' + mode)

with open(sys.argv[1], 'wb') as f:
    record = (
        struct.pack('<Q', len(header))
        + struct.pack('<Q', len(witness_state))
        + header
        + witness_state
    )
    f.write(record)
    pad = (-len(record)) % 8
    if pad: f.write(b'\\x00' * pad)

with open(sys.argv[2], 'wb') as f:
    f.write(expected)
" "$in_file" "$exp_file"

  "$ZISKEMU" -e gen-out/zisk_parent_state_root_present_in_witness_state.elf \
    -i "$in_file" -o "$out_file" -n 4000000 \
    >"$REPO_ROOT/gen-out/zisk_psrp_${name}.emu.log" 2>&1 || true

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
# 1) state_root IS the single leaf's keccak -> present.
run_case "root_is_single_leaf"          single_leaf || FAILED=1
# 2) state_root is one entry among many -> present.
run_case "root_in_multi_entry"          multi_entry_with_root || FAILED=1
# 3) witness.state empty -> absent.
run_case "empty_witness_state"          empty_state || FAILED=1
# 4) witness.state has only unrelated nodes -> absent.
run_case "other_nodes_only"             other_nodes_only || FAILED=1
# 5) Header too small to parse -> status 1, is_present 0.
run_case "garbage_header"               garbage_header || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: parent_state_root_present_in_witness_state end-to-end"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
