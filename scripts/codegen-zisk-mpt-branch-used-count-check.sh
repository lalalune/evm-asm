#!/usr/bin/env bash
# codegen-zisk-mpt-branch-used-count-check.sh -- PR-K117.
#
# Count non-empty child slots in an MPT branch node.
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

echo "==> emit zisk_mpt_branch_used_count ELF"
lake exe codegen --program zisk_mpt_branch_used_count --halt linux93 \
  -o gen-out/zisk_mpt_branch_used_count

REPO_ROOT="$(pwd)"

# run_case <name> <kind> <used_indices_csv_or_empty> <expected_status>
run_case() {
  local name="$1" kind="$2" used_csv="$3" exp_status="${4:-0}"

  local in_file="$REPO_ROOT/gen-out/zisk_mpt_branch_used_count_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_mpt_branch_used_count_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys, rlp
kind = '$kind'
used = [int(n) for n in '$used_csv'.split(',') if n.strip()]

if kind == 'branch':
    children = []
    for i in range(16):
        if i in used:
            children.append(bytes([0xaa]*32))
        else:
            children.append(b'')
    node = children + [b'']
elif kind == 'branch_with_value':
    children = []
    for i in range(16):
        if i in used:
            children.append(bytes([0xaa]*32))
        else:
            children.append(b'')
    node = children + [b'some-terminal-value']
elif kind == 'leaf':
    node = [b'\x20', b'value']
elif kind == 'invalid':
    node = [b''] * 7
else:
    raise ValueError(kind)

node_rlp = rlp.encode(node)
with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(node_rlp)))
    f.write(node_rlp)
    pad = (-(8 + len(node_rlp))) % 8
    if pad: f.write(b'\x00' * pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_mpt_branch_used_count.elf \
    -i "$in_file" -o "$out_file" -n 5000000 \
    >"$REPO_ROOT/gen-out/zisk_mpt_branch_used_count_${name}.emu.log" 2>&1 || true

  local actual_status; actual_status="$(xxd -p -l 8 "$out_file" | tr -d '\n')"
  local exp_status_le; exp_status_le="$(python3 -c "print(int('$exp_status').to_bytes(8, 'little').hex())")"

  if [[ "$actual_status" != "$exp_status_le" ]]; then
    printf "  %-32s FAIL status=0x%s expected=%d\n" "$name" "$actual_status" "$exp_status"
    return 1
  fi
  if [[ "$exp_status" != "0" ]]; then
    printf "  %-32s OK   status=%d (rejected)\n" "$name" "$exp_status"
    return 0
  fi
  local actual_count_le; actual_count_le="$(dd if="$out_file" bs=1 skip=8 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local actual_count; actual_count="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$actual_count_le'))[0])")"
  local expected_count; expected_count="$(python3 -c "print(len([n for n in '$used_csv'.split(',') if n.strip()]))")"
  if [[ "$actual_count" == "$expected_count" ]]; then
    printf "  %-32s OK   used=%d\n" "$name" "$expected_count"
    return 0
  else
    printf "  %-32s FAIL used=%d expected=%d\n" "$name" "$actual_count" "$expected_count"
    return 1
  fi
}

FAILED=0
run_case "empty_branch"          branch              ""                       || FAILED=1
run_case "one_child"             branch              "0"                      || FAILED=1
run_case "two_children"          branch              "0,15"                   || FAILED=1
run_case "five_children"         branch              "0,3,7,11,15"            || FAILED=1
run_case "all_16_children"       branch              "0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15" || FAILED=1
run_case "value_only"            branch_with_value   ""                       || FAILED=1
run_case "kids_and_value"        branch_with_value   "5,10"                   || FAILED=1
# Rejections
run_case "leaf_node"             leaf                ""           1 || FAILED=1
run_case "seven_item_node"       invalid             ""           1 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: mpt_branch_used_count counts non-empty child slots"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
