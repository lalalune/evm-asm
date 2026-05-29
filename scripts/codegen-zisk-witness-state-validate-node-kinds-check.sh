#!/usr/bin/env bash
# codegen-zisk-witness-state-validate-node-kinds-check.sh
#
# Walks the SSZ witness.state list and calls mpt_node_kind (K21)
# on every entry. Verifies that every entry parses as one of
# Leaf / Extension / Branch. Reports the index of the first
# malformed entry, else the total node count N.
#
# Useful for up-front witness sanity-checking: catches
# structurally bad SSZ entries before mpt_walk hits them.
#
# Output (24 bytes):
#   bytes  0.. 8 : status (0 ok / 1 parse fail)
#   bytes  8..16 : n_processed (= N on success; first bad index on fail)
#   bytes 16..24 : first_bad_index (0xFF..FF on success)
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

echo "==> emit zisk_witness_state_validate_node_kinds ELF"
lake exe codegen --program zisk_witness_state_validate_node_kinds \
  --halt linux93 \
  -o gen-out/zisk_witness_state_validate_node_kinds

REPO_ROOT="$(pwd)"

# run_case <name> <mode> [args...]
#
#   empty
#   leafs_only <count>
#   mixed_leaf_ext_branch
#   parse_fail_at <bad_idx>
run_case() {
  local name="$1"; shift
  local mode="$1"; shift

  local in_file="$REPO_ROOT/gen-out/zisk_wsvn_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_wsvn_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_wsvn_${name}.expected"

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

def some_leaf(seed):
    return leaf_node([seed & 0xf, (seed >> 4) & 0xf, 1, 2, 3, 4], b'\\x42' * 5)

def some_extension():
    # Extension node points at a 32-byte ref.
    return extension_node([1, 2, 3], b'\\x33' * 32)

def some_branch():
    # 17 children: 16 32-byte hashes + 1 empty value.
    children = [b'\\x44' * 32 for _ in range(16)]
    value = b''
    return branch_node(children, value)

if mode == 'empty':
    elements = []
    expected_n = 0
    expected_bad = MAX64
    expected_status = 0
elif mode == 'leafs_only':
    count = int(parts[0])
    elements = [some_leaf(i) for i in range(count)]
    expected_n = count
    expected_bad = MAX64
    expected_status = 0
elif mode == 'mixed_leaf_ext_branch':
    elements = [
        some_leaf(0),
        some_extension(),
        some_branch(),
        some_leaf(1),
    ]
    expected_n = 4
    expected_bad = MAX64
    expected_status = 0
elif mode == 'parse_fail_at':
    bad_idx = int(parts[0])
    elements = [some_leaf(i) for i in range(bad_idx + 2)]
    # Replace element bad_idx with an invalid (non-list-RLP) byte.
    elements[bad_idx] = b'\\x00'
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

  "$ZISKEMU" -e gen-out/zisk_witness_state_validate_node_kinds.elf \
    -i "$in_file" -o "$out_file" -n 4000000 \
    >"$REPO_ROOT/gen-out/zisk_wsvn_${name}.emu.log" 2>&1 || true

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
run_case "one_leaf"           leafs_only 1 || FAILED=1
run_case "five_leafs"         leafs_only 5 || FAILED=1
run_case "mixed_kinds"        mixed_leaf_ext_branch || FAILED=1
run_case "parse_fail_at_0"    parse_fail_at 0 || FAILED=1
run_case "parse_fail_at_2"    parse_fail_at 2 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: witness_state_validate_node_kinds end-to-end"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
