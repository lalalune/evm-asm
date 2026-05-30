#!/usr/bin/env bash
# codegen-zisk-witness-storage-node-kind-distribution-check.sh
#
# Storage-side mirror of #7207. Classifies each entry in
# witness.storage by K22 mpt_node_kind, returns per-kind
# counts in a 32-byte buffer.
#
# Output (40 bytes):
#   bytes  0.. 8 : status (always 0)
#   bytes  8..16 : count_branch
#   bytes 16..24 : count_extension
#   bytes 24..32 : count_leaf
#   bytes 32..40 : count_parse_fail
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

echo "==> emit zisk_witness_storage_node_kind_distribution ELF"
lake exe codegen --program zisk_witness_storage_node_kind_distribution \
  --halt linux93 \
  -o gen-out/zisk_witness_storage_node_kind_distribution

REPO_ROOT="$(pwd)"

run_case() {
  local name="$1"; shift
  local mode="$1"; shift

  local in_file="$REPO_ROOT/gen-out/zisk_wznd_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_wznd_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_wznd_${name}.expected"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys
import rlp

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

def extension_node(path_nibbles, child_ref):
    return rlp.encode([hp_encode(path_nibbles, False), child_ref])

def branch_node():
    return rlp.encode([b''] * 16 + [b''])

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

if mode == 'empty':
    entries = []
    expected_counts = (0, 0, 0, 0)
elif mode == 'single_slot_leaf':
    # Typical storage trie with one populated slot: single leaf.
    entries = [leaf_node(bytes_to_nibbles(b'\\xaa'*32), b'\\x42')]
    expected_counts = (0, 0, 1, 0)
elif mode == 'branch_plus_two_leaves':
    # Branch root + two slot leaves.
    entries = [
        branch_node(),
        leaf_node(bytes_to_nibbles(b'\\xaa'*31), b'\\x10'),
        leaf_node(bytes_to_nibbles(b'\\xbb'*31), b'\\x20'),
    ]
    expected_counts = (1, 0, 2, 0)
elif mode == 'extension_chain':
    entries = [
        extension_node(bytes_to_nibbles(b'\\x00')[:1], b'\\xcc'*32),
        leaf_node(bytes_to_nibbles(b'\\xee'*32), b'\\x99'),
    ]
    expected_counts = (0, 1, 1, 0)
elif mode == 'garbage_mixed':
    entries = [
        leaf_node(bytes_to_nibbles(b'\\xaa'*32), b'\\x42'),
        b'\\xff',
        branch_node(),
        b'\\xff',
    ]
    expected_counts = (1, 0, 1, 2)
else:
    raise SystemExit('bad mode: ' + mode)

witness_storage = build_ssz_section(entries)

expected = struct.pack('<Q', 0)
for c in expected_counts:
    expected += struct.pack('<Q', c)

with open(sys.argv[1], 'wb') as f:
    record = struct.pack('<Q', len(witness_storage)) + witness_storage
    f.write(record)
    pad = (-len(record)) % 8
    if pad: f.write(b'\\x00' * pad)

with open(sys.argv[2], 'wb') as f:
    f.write(expected)
" "$in_file" "$exp_file"

  "$ZISKEMU" -e gen-out/zisk_witness_storage_node_kind_distribution.elf \
    -i "$in_file" -o "$out_file" -n 4000000 \
    >"$REPO_ROOT/gen-out/zisk_wznd_${name}.emu.log" 2>&1 || true

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
run_case "empty_section"                  empty || FAILED=1
run_case "single_slot_leaf"               single_slot_leaf || FAILED=1
run_case "branch_plus_two_leaves"         branch_plus_two_leaves || FAILED=1
run_case "extension_chain"                extension_chain || FAILED=1
run_case "garbage_mixed_with_real"        garbage_mixed || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: witness_storage_node_kind_distribution end-to-end"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
