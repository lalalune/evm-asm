#!/usr/bin/env bash
# codegen-zisk-mpt-nibbles-to-compact-check.sh -- PR-K109.
#
# Pack nibble-list into MPT compact (hex-prefix) encoding.
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

echo "==> emit zisk_mpt_nibbles_to_compact ELF"
lake exe codegen --program zisk_mpt_nibbles_to_compact --halt linux93 \
  -o gen-out/zisk_mpt_nibbles_to_compact

REPO_ROOT="$(pwd)"

# run_case <name> <nibbles_csv> <is_leaf>
run_case() {
  local name="$1" nibbles_csv="$2" is_leaf="$3"

  local in_file="$REPO_ROOT/gen-out/zisk_mpt_nibbles_to_compact_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_mpt_nibbles_to_compact_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys
from ethereum.forks.amsterdam.trie import nibble_list_to_compact
nibs_csv = '$nibbles_csv'
nibs = [int(n) for n in nibs_csv.split(',') if n.strip()] if nibs_csv else []
is_leaf = bool($is_leaf)
expected = bytes(nibble_list_to_compact(bytes(nibs), is_leaf))

with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(nibs)))
    f.write(struct.pack('<Q', 1 if is_leaf else 0))
    f.write(bytes(nibs))
    pad = (-(16 + len(nibs))) % 8
    if pad: f.write(b'\x00' * pad)

with open(sys.argv[1] + '.expected', 'wb') as f:
    f.write(struct.pack('<Q', len(expected)))
    f.write(expected)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_mpt_nibbles_to_compact.elf \
    -i "$in_file" -o "$out_file" -n 1000000 \
    >"$REPO_ROOT/gen-out/zisk_mpt_nibbles_to_compact_${name}.emu.log" 2>&1 || true

  local actual_status; actual_status="$(xxd -p -l 8 "$out_file" | tr -d '\n')"
  local actual_len_le; actual_len_le="$(dd if="$out_file" bs=1 skip=8 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local actual_len; actual_len="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$actual_len_le'))[0])")"
  local expected_len_le; expected_len_le="$(dd if="$in_file.expected" bs=1 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local expected_len; expected_len="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$expected_len_le'))[0])")"

  if [[ "$actual_status" != "0000000000000000" ]]; then
    printf "  %-32s FAIL status=0x%s\n" "$name" "$actual_status"
    return 1
  fi
  if [[ "$actual_len" != "$expected_len" ]]; then
    printf "  %-32s FAIL len=%d expected=%d\n" "$name" "$actual_len" "$expected_len"
    return 1
  fi
  local actual_bytes; actual_bytes="$(dd if="$out_file" bs=1 skip=16 count="$actual_len" 2>/dev/null | xxd -p | tr -d '\n')"
  local expected_bytes; expected_bytes="$(dd if="$in_file.expected" bs=1 skip=8 count="$expected_len" 2>/dev/null | xxd -p | tr -d '\n')"
  if [[ "$actual_bytes" == "$expected_bytes" ]]; then
    printf "  %-32s OK   len=%d bytes=%s\n" "$name" "$expected_len" "${expected_bytes:0:20}"
    return 0
  else
    printf "  %-32s FAIL bytes mismatch\n    expected: %s\n    actual:   %s\n" "$name" "$expected_bytes" "$actual_bytes"
    return 1
  fi
}

FAILED=0
run_case "empty_extension"     ""                 0 || FAILED=1
run_case "empty_leaf"          ""                 1 || FAILED=1
run_case "single_ext"          "5"                0 || FAILED=1
run_case "single_leaf"         "7"                1 || FAILED=1
run_case "two_ext"             "1,2"              0 || FAILED=1
run_case "two_leaf"            "9,10"             1 || FAILED=1
run_case "three_ext"           "1,2,3"            0 || FAILED=1
run_case "three_leaf"          "15,14,13"         1 || FAILED=1
run_case "addr_prefix_ext"     "$(python3 -c "print(','.join(str(i & 0xf) for i in range(20)))")"           0 || FAILED=1
run_case "addr_prefix_leaf"    "$(python3 -c "print(','.join(str(i & 0xf) for i in range(20)))")"           1 || FAILED=1
# Long: 64-nibble account path
run_case "full_address_leaf"   "$(python3 -c "print(','.join(str(i & 0xf) for i in range(64)))")"           1 || FAILED=1
run_case "full_address_ext"    "$(python3 -c "print(','.join(str(i & 0xf) for i in range(64)))")"           0 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: mpt_nibbles_to_compact matches nibble_list_to_compact"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
