#!/usr/bin/env bash
# codegen-zisk-mpt-compact-to-nibbles-check.sh -- PR-K110.
#
# Decode MPT compact (hex-prefix) → (nibble list, is_leaf).
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

echo "==> emit zisk_mpt_compact_to_nibbles ELF"
lake exe codegen --program zisk_mpt_compact_to_nibbles --halt linux93 \
  -o gen-out/zisk_mpt_compact_to_nibbles

REPO_ROOT="$(pwd)"

# run_case <name> <nibbles_csv> <is_leaf>
# Round-trips: nibbles → compact (via Python) → ziskemu decoder → assert nibbles + is_leaf.
run_case() {
  local name="$1" nibbles_csv="$2" is_leaf="$3"

  local in_file="$REPO_ROOT/gen-out/zisk_mpt_compact_to_nibbles_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_mpt_compact_to_nibbles_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys
from ethereum.forks.amsterdam.trie import nibble_list_to_compact
nibs_csv = '$nibbles_csv'
nibs = [int(n) for n in nibs_csv.split(',') if n.strip()] if nibs_csv else []
is_leaf = bool($is_leaf)
compact = bytes(nibble_list_to_compact(bytes(nibs), is_leaf))

with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(compact)))
    f.write(compact)
    pad = (-(8 + len(compact))) % 8
    if pad: f.write(b'\x00' * pad)

with open(sys.argv[1] + '.expected', 'wb') as f:
    f.write(struct.pack('<Q', len(nibs)))
    f.write(struct.pack('<Q', 1 if is_leaf else 0))
    f.write(bytes(nibs))
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_mpt_compact_to_nibbles.elf \
    -i "$in_file" -o "$out_file" -n 1000000 \
    >"$REPO_ROOT/gen-out/zisk_mpt_compact_to_nibbles_${name}.emu.log" 2>&1 || true

  local actual_status; actual_status="$(xxd -p -l 8 "$out_file" | tr -d '\n')"
  local actual_count_le; actual_count_le="$(dd if="$out_file" bs=1 skip=8 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local actual_count; actual_count="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$actual_count_le'))[0])")"
  local actual_isleaf_le; actual_isleaf_le="$(dd if="$out_file" bs=1 skip=16 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local actual_isleaf; actual_isleaf="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$actual_isleaf_le'))[0])")"

  local expected_count_le; expected_count_le="$(dd if="$in_file.expected" bs=1 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local expected_count; expected_count="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$expected_count_le'))[0])")"
  local expected_isleaf; expected_isleaf="$is_leaf"

  if [[ "$actual_status" != "0000000000000000" ]]; then
    printf "  %-32s FAIL status=0x%s\n" "$name" "$actual_status"
    return 1
  fi
  if [[ "$actual_count" != "$expected_count" || "$actual_isleaf" != "$expected_isleaf" ]]; then
    printf "  %-32s FAIL count=%d expected=%d is_leaf=%d expected=%d\n" "$name" "$actual_count" "$expected_count" "$actual_isleaf" "$expected_isleaf"
    return 1
  fi
  if [[ "$expected_count" -gt 0 ]]; then
    local actual_nibbles; actual_nibbles="$(dd if="$out_file" bs=1 skip=24 count="$expected_count" 2>/dev/null | xxd -p | tr -d '\n')"
    local expected_nibbles; expected_nibbles="$(dd if="$in_file.expected" bs=1 skip=16 count="$expected_count" 2>/dev/null | xxd -p | tr -d '\n')"
    if [[ "$actual_nibbles" != "$expected_nibbles" ]]; then
      printf "  %-32s FAIL nibble mismatch\n    expected: %s\n    actual:   %s\n" "$name" "$expected_nibbles" "$actual_nibbles"
      return 1
    fi
  fi
  printf "  %-32s OK   count=%d is_leaf=%d\n" "$name" "$expected_count" "$expected_isleaf"
  return 0
}

FAILED=0
run_case "empty_ext"           ""                  0 || FAILED=1
run_case "empty_leaf"          ""                  1 || FAILED=1
run_case "single_ext"          "5"                 0 || FAILED=1
run_case "single_leaf"         "7"                 1 || FAILED=1
run_case "two_ext"             "1,2"               0 || FAILED=1
run_case "two_leaf"            "9,10"              1 || FAILED=1
run_case "three_ext"           "1,2,3"             0 || FAILED=1
run_case "three_leaf"          "15,14,13"          1 || FAILED=1
run_case "addr_prefix_ext"     "$(python3 -c "print(','.join(str(i & 0xf) for i in range(20)))")" 0 || FAILED=1
run_case "addr_prefix_leaf"    "$(python3 -c "print(','.join(str(i & 0xf) for i in range(20)))")" 1 || FAILED=1
run_case "full_address_leaf"   "$(python3 -c "print(','.join(str(i & 0xf) for i in range(64)))")" 1 || FAILED=1
run_case "full_address_ext"    "$(python3 -c "print(','.join(str(i & 0xf) for i in range(64)))")" 0 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: mpt_compact_to_nibbles round-trips against nibble_list_to_compact"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
