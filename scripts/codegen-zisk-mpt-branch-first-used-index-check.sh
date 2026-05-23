#!/usr/bin/env bash
# codegen-zisk-mpt-branch-first-used-index-check.sh -- PR-K118.
#
# Return lowest-indexed non-empty child slot of an MPT branch.
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

echo "==> emit zisk_mpt_branch_first_used_index ELF"
lake exe codegen --program zisk_mpt_branch_first_used_index --halt linux93 \
  -o gen-out/zisk_mpt_branch_first_used_index

REPO_ROOT="$(pwd)"

# run_case <name> <kind> <used_indices_csv_or_empty> <expected_status>
run_case() {
  local name="$1" kind="$2" used_csv="$3" exp_status="${4:-0}"

  local in_file="$REPO_ROOT/gen-out/zisk_mpt_branch_first_used_index_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_mpt_branch_first_used_index_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys, rlp
kind = '$kind'
used = [int(n) for n in '$used_csv'.split(',') if n.strip()]

if kind == 'branch':
    children = [bytes([0xaa]*32) if i in used else b'' for i in range(16)]
    node = children + [b'']
elif kind == 'branch_with_value':
    children = [bytes([0xaa]*32) if i in used else b'' for i in range(16)]
    node = children + [b'terminal']
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

  "$ZISKEMU" -e gen-out/zisk_mpt_branch_first_used_index.elf \
    -i "$in_file" -o "$out_file" -n 5000000 \
    >"$REPO_ROOT/gen-out/zisk_mpt_branch_first_used_index_${name}.emu.log" 2>&1 || true

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
  local actual_idx_le; actual_idx_le="$(dd if="$out_file" bs=1 skip=8 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local actual_idx; actual_idx="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$actual_idx_le'))[0])")"
  local expected_idx; expected_idx="$(python3 -c "
used = [int(n) for n in '$used_csv'.split(',') if n.strip()]
print(min(used) if used else 16)")"
  if [[ "$actual_idx" == "$expected_idx" ]]; then
    printf "  %-32s OK   first_index=%d\n" "$name" "$expected_idx"
    return 0
  else
    printf "  %-32s FAIL first_index=%d expected=%d\n" "$name" "$actual_idx" "$expected_idx"
    return 1
  fi
}

FAILED=0
run_case "empty_branch"        branch              ""                       || FAILED=1
run_case "child_at_0"          branch              "0"                      || FAILED=1
run_case "child_at_15"         branch              "15"                     || FAILED=1
run_case "first_of_two"        branch              "3,10"                   || FAILED=1
run_case "first_at_7"          branch              "7,11"                   || FAILED=1
run_case "all_16"              branch              "0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15" || FAILED=1
run_case "value_only"          branch_with_value   ""                       || FAILED=1
run_case "kid_5_with_value"    branch_with_value   "5"                      || FAILED=1
# Rejections
run_case "leaf_node"           leaf                ""           1 || FAILED=1
run_case "seven_item_node"     invalid             ""           1 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: mpt_branch_first_used_index returns lowest non-empty child index"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
