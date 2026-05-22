#!/usr/bin/env bash
# codegen-zisk-mpt-branch-get-child-check.sh -- PR-K115.
#
# Extract i-th child reference of a 17-item branch node.
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

echo "==> emit zisk_mpt_branch_get_child ELF"
lake exe codegen --program zisk_mpt_branch_get_child --halt linux93 \
  -o gen-out/zisk_mpt_branch_get_child

REPO_ROOT="$(pwd)"

# run_case <name> <kind> <index> <expected_child_hex_or_empty>
# kind: "branch_default", "leaf", "ext", "thirteen_items"
run_case() {
  local name="$1" kind="$2" idx="$3" exp_child_hex="$4" exp_status="${5:-0}"

  local in_file="$REPO_ROOT/gen-out/zisk_mpt_branch_get_child_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_mpt_branch_get_child_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys, rlp
kind = '$kind'

if kind == 'branch_default':
    children = []
    for i in range(16):
        if i == 0:
            children.append(bytes([0xaa] * 32))
        elif i == 5:
            children.append(bytes([0xbb] * 32))
        elif i == 15:
            children.append(bytes([0xcc] * 32))
        elif i == 3:
            children.append(bytes.fromhex('c102'))  # embedded
        else:
            children.append(b'')
    node = children + [b'branch_value']
elif kind == 'leaf':
    node = [b'\x20', b'value']
elif kind == 'ext':
    node = [b'\x00', bytes([0xab]*32)]
elif kind == 'thirteen_items':
    node = [b''] * 13
else:
    raise ValueError(kind)

node_rlp = rlp.encode(node)
with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(node_rlp)))
    f.write(struct.pack('<Q', $idx))
    f.write(node_rlp)
    pad = (-(16 + len(node_rlp))) % 8
    if pad: f.write(b'\x00' * pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_mpt_branch_get_child.elf \
    -i "$in_file" -o "$out_file" -n 5000000 \
    >"$REPO_ROOT/gen-out/zisk_mpt_branch_get_child_${name}.emu.log" 2>&1 || true

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
  local actual_child_len_le; actual_child_len_le="$(dd if="$out_file" bs=1 skip=16 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local actual_child_len; actual_child_len="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$actual_child_len_le'))[0])")"
  local expected_len; expected_len="$(python3 -c "print(len(bytes.fromhex('$exp_child_hex')))")"
  if [[ "$actual_child_len" != "$expected_len" ]]; then
    printf "  %-32s FAIL child_len=%d expected=%d\n" "$name" "$actual_child_len" "$expected_len"
    return 1
  fi
  if [[ "$expected_len" -gt 0 ]]; then
    # Need to read child bytes from input file at the reported offset.
    local offset_le; offset_le="$(dd if="$out_file" bs=1 skip=8 count=8 2>/dev/null | xxd -p | tr -d '\n')"
    local offset; offset="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$offset_le'))[0])")"
    local file_off=$((16 + offset))  # skip 8B len + 8B idx + offset into rlp
    local actual_bytes; actual_bytes="$(dd if="$in_file" bs=1 skip="$file_off" count="$expected_len" 2>/dev/null | xxd -p | tr -d '\n')"
    if [[ "$actual_bytes" != "$exp_child_hex" ]]; then
      printf "  %-32s FAIL\n    expected: %s\n    actual:   %s\n" "$name" "${exp_child_hex:0:40}" "${actual_bytes:0:40}"
      return 1
    fi
  fi
  printf "  %-32s OK   len=%d\n" "$name" "$expected_len"
  return 0
}

FAILED=0
H_AA="$(python3 -c "print('aa' * 32)")"
H_BB="$(python3 -c "print('bb' * 32)")"
H_CC="$(python3 -c "print('cc' * 32)")"

run_case "idx_0_aa"     branch_default 0  "$H_AA"   || FAILED=1
run_case "idx_5_bb"     branch_default 5  "$H_BB"   || FAILED=1
run_case "idx_15_cc"    branch_default 15 "$H_CC"   || FAILED=1
run_case "idx_3_embed"  branch_default 3  "c102"    || FAILED=1
run_case "idx_7_empty"  branch_default 7  ""        || FAILED=1
# Rejections
run_case "leaf_node"           leaf         0  ""    1 || FAILED=1
run_case "ext_node"            ext          0  ""    1 || FAILED=1
run_case "thirteen_item_node"  thirteen_items 0 ""   1 || FAILED=1
run_case "idx_16_oob"          branch_default 16 ""  2 || FAILED=1
run_case "idx_99_oob"          branch_default 99 ""  2 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: mpt_branch_get_child returns i-th child reference"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
