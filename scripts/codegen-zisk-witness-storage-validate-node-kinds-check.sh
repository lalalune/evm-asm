#!/usr/bin/env bash
# codegen-zisk-witness-storage-validate-node-kinds-check.sh
#
# Walks the SSZ witness.storage list and calls mpt_node_kind (K21)
# on every entry. Verifies every entry parses as one of
# Leaf / Extension / Branch.
#
# Storage-trie sibling of PR #7178 witness_state_validate_node_kinds:
# same iteration, same per-element check, different witness section.
#
# Output (24 bytes):
#   bytes  0.. 8 : status (0 ok / 1 parse fail)
#   bytes  8..16 : n_processed
#   bytes 16..24 : first_bad_index
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

echo "==> emit zisk_witness_storage_validate_node_kinds ELF"
lake exe codegen --program zisk_witness_storage_validate_node_kinds \
  --halt linux93 \
  -o gen-out/zisk_witness_storage_validate_node_kinds

REPO_ROOT="$(pwd)"

run_case() {
  local name="$1"; shift
  local mode="$1"; shift

  local in_file="$REPO_ROOT/gen-out/zisk_wsgvn_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_wsgvn_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_wsgvn_${name}.expected"

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

def branch_node(children, value):
    return rlp.encode(children + [value])

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

argv = sys.argv[1:]
mode = '$mode'
parts = [
$(for arg in "$@"; do printf '  %s,\n' "\"$arg\""; done)
]

MAX64 = (1 << 64) - 1

def storage_leaf(slot_value_int):
    # Slot MPT leaf: 64-nibble path + rlp(slot_value).
    path = [i & 0xf for i in range(64)]
    return leaf_node(path, rlp.encode(slot_value_int))

def storage_extension():
    return extension_node([1, 2, 3, 4], b'\\x55' * 32)

def storage_branch():
    children = [b'\\x66' * 32 for _ in range(16)]
    return branch_node(children, b'')

if mode == 'empty':
    elements = []
    expected_n = 0
    expected_bad = MAX64
    expected_status = 0
elif mode == 'leafs_only':
    count = int(parts[0])
    elements = [storage_leaf(i + 1) for i in range(count)]
    expected_n = count
    expected_bad = MAX64
    expected_status = 0
elif mode == 'mixed_kinds':
    elements = [
        storage_leaf(42),
        storage_extension(),
        storage_branch(),
        storage_leaf(100),
    ]
    expected_n = 4
    expected_bad = MAX64
    expected_status = 0
elif mode == 'parse_fail_at':
    bad_idx = int(parts[0])
    elements = [storage_leaf(i + 1) for i in range(bad_idx + 2)]
    elements[bad_idx] = b'\\x00'                # garbage byte (not list RLP)
    expected_n = bad_idx
    expected_bad = bad_idx
    expected_status = 1
else:
    raise SystemExit('bad mode: ' + mode)

section = build_ssz_section(elements)
expected = (
    struct.pack('<Q', expected_status)
    + struct.pack('<Q', expected_n)
    + struct.pack('<Q', expected_bad)
)

with open(argv[0], 'wb') as f:
    record = struct.pack('<Q', len(section)) + section
    f.write(record)
    pad = (-len(record)) % 8
    if pad: f.write(b'\\x00' * pad)

with open(argv[1], 'wb') as f:
    f.write(expected)
" "$in_file" "$exp_file"

  "$ZISKEMU" -e gen-out/zisk_witness_storage_validate_node_kinds.elf \
    -i "$in_file" -o "$out_file" -n 4000000 \
    >"$REPO_ROOT/gen-out/zisk_wsgvn_${name}.emu.log" 2>&1 || true

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
run_case "empty_section"      empty || FAILED=1
run_case "one_slot_leaf"      leafs_only 1 || FAILED=1
run_case "many_slot_leafs"    leafs_only 5 || FAILED=1
run_case "mixed_kinds"        mixed_kinds || FAILED=1
run_case "parse_fail_at_0"    parse_fail_at 0 || FAILED=1
run_case "parse_fail_at_2"    parse_fail_at 2 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: witness_storage_validate_node_kinds end-to-end"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
