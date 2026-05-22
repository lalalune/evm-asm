#!/usr/bin/env bash
# codegen-zisk-mpt-branch-get-value-check.sh -- PR-K116.
#
# Extract field 16 (value) of a 17-item branch node.
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

echo "==> emit zisk_mpt_branch_get_value ELF"
lake exe codegen --program zisk_mpt_branch_get_value --halt linux93 \
  -o gen-out/zisk_mpt_branch_get_value

REPO_ROOT="$(pwd)"

# run_case <name> <kind> <value_hex> <expected_status>
run_case() {
  local name="$1" kind="$2" value_hex="$3" exp_status="${4:-0}"

  local in_file="$REPO_ROOT/gen-out/zisk_mpt_branch_get_value_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_mpt_branch_get_value_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys, rlp
kind = '$kind'
value = bytes.fromhex('$value_hex')

if kind == 'branch':
    children = [b''] * 16
    node = children + [value]
elif kind == 'branch_with_kids':
    children = [bytes([0xaa]*32)] * 16
    node = children + [value]
elif kind == 'leaf':
    node = [b'\x20', value]
elif kind == 'invalid':
    node = [b''] * 5
else:
    raise ValueError(kind)

node_rlp = rlp.encode(node)
with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(node_rlp)))
    f.write(node_rlp)
    pad = (-(8 + len(node_rlp))) % 8
    if pad: f.write(b'\x00' * pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_mpt_branch_get_value.elf \
    -i "$in_file" -o "$out_file" -n 5000000 \
    >"$REPO_ROOT/gen-out/zisk_mpt_branch_get_value_${name}.emu.log" 2>&1 || true

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
  local actual_value_len_le; actual_value_len_le="$(dd if="$out_file" bs=1 skip=16 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local actual_value_len; actual_value_len="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$actual_value_len_le'))[0])")"
  local expected_len; expected_len="$(python3 -c "print(len(bytes.fromhex('$value_hex')))")"
  if [[ "$actual_value_len" != "$expected_len" ]]; then
    printf "  %-32s FAIL value_len=%d expected=%d\n" "$name" "$actual_value_len" "$expected_len"
    return 1
  fi
  if [[ "$expected_len" -gt 0 ]]; then
    local offset_le; offset_le="$(dd if="$out_file" bs=1 skip=8 count=8 2>/dev/null | xxd -p | tr -d '\n')"
    local offset; offset="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$offset_le'))[0])")"
    local file_off=$((8 + offset))
    local actual_bytes; actual_bytes="$(dd if="$in_file" bs=1 skip="$file_off" count="$expected_len" 2>/dev/null | xxd -p | tr -d '\n')"
    if [[ "$actual_bytes" != "$value_hex" ]]; then
      printf "  %-32s FAIL\n    expected: %s\n    actual:   %s\n" "$name" "${value_hex:0:40}" "${actual_bytes:0:40}"
      return 1
    fi
  fi
  printf "  %-32s OK   value_len=%d\n" "$name" "$expected_len"
  return 0
}

FAILED=0
run_case "empty_value"          branch              ""             || FAILED=1
run_case "short_value"          branch              "deadbeef"     || FAILED=1
run_case "32B_value"            branch              "$(python3 -c "print('ee' * 32)")" || FAILED=1
run_case "branch_with_kids_value" branch_with_kids  "feedface"     || FAILED=1
run_case "long_value"           branch              "$(python3 -c "print('cd' * 200)")" || FAILED=1
# Rejections
run_case "leaf_node"            leaf                "0000"      1 || FAILED=1
run_case "five_item_node"       invalid             ""          1 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: mpt_branch_get_value extracts field 16"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
