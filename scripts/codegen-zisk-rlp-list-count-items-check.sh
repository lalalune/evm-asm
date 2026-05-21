#!/usr/bin/env bash
# codegen-zisk-rlp-list-count-items-check.sh -- PR-K47.
#
# Count top-level items in an RLP-encoded list. Building
# block for access_list / authorization_list / blob hashes
# cardinality.
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

echo "==> emit zisk_rlp_list_count_items ELF"
lake exe codegen --program zisk_rlp_list_count_items --halt linux93 \
  -o gen-out/zisk_rlp_list_count_items

REPO_ROOT="$(pwd)"

# run_case <name> <expected_status> <expected_count> <items_json>
# items_json is a Python list of either ints or hex strings or nested lists.
run_case() {
  local name="$1" expected_status="$2" expected_count="$3" items_json="$4"

  local in_file="$REPO_ROOT/gen-out/zisk_rlp_list_count_items_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_rlp_list_count_items_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import json, struct, sys
import rlp

raw_items = json.loads('''$items_json''')

# Convert: dict entries with 'hex' key become bytes; lists recursively; ints stay.
def conv(x):
    if isinstance(x, list):
        return [conv(e) for e in x]
    if isinstance(x, dict) and 'hex' in x:
        return bytes.fromhex(x['hex'])
    return x

items = conv(raw_items)
list_rlp = rlp.encode(items)
with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(list_rlp)))
    f.write(list_rlp)
    pad = (-(8 + len(list_rlp))) % 8
    if pad:
        f.write(b'\x00' * pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_rlp_list_count_items.elf \
    -i "$in_file" -o "$out_file" -n 500000 \
    >"$REPO_ROOT/gen-out/zisk_rlp_list_count_items_${name}.emu.log" 2>&1 || true

  local actual_status; actual_status="$(xxd -p -l 8 "$out_file" 2>/dev/null | tr -d '\n')"
  local actual_count; actual_count="$(dd if="$out_file" bs=1 skip=8 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local exp_status_le; exp_status_le="$(python3 -c "print(int('$expected_status').to_bytes(8, 'little').hex())")"
  local exp_count_le; exp_count_le="$(python3 -c "print(int('$expected_count').to_bytes(8, 'little').hex())")"

  if [[ "$actual_status" == "$exp_status_le" && "$actual_count" == "$exp_count_le" ]]; then
    printf "  %-30s OK   status=%d count=%d\n" "$name" "$expected_status" "$expected_count"
    return 0
  else
    printf "  %-30s FAIL  expected status=%d count=%d got status=0x%s count=0x%s\n" \
      "$name" "$expected_status" "$expected_count" "$actual_status" "$actual_count"
    return 1
  fi
}

# Some scrap addresses + slot hashes
ALICE='{"hex": "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"}'
BOB='{"hex": "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"}'
CAROL='{"hex": "cccccccccccccccccccccccccccccccccccccccc"}'
SLOT1='{"hex": "5555555555555555555555555555555555555555555555555555555555555555"}'
SLOT2='{"hex": "6666666666666666666666666666666666666666666666666666666666666666"}'

FAILED=0
# Edge cases
run_case "empty"                  0 0  "[]"                                                        || FAILED=1
run_case "one_int"                0 1  "[7]"                                                       || FAILED=1
run_case "one_byte_zero"          0 1  "[0]"                                                       || FAILED=1
run_case "two_ints"               0 2  "[1, 2]"                                                    || FAILED=1
# Mix of item shapes
run_case "mixed_singles"          0 4  "[0, 7, 127, 128]"                                          || FAILED=1
run_case "short_strings"          0 3  "[\"abc\", \"defghij\", \"k\"]"                             || FAILED=1
# Long string (>=56 bytes) — long-string RLP prefix path
LONG_STR_56='{"hex": "'"$(printf '11%.0s' $(seq 1 56))"'"}'
LONG_STR_300='{"hex": "'"$(printf '22%.0s' $(seq 1 300))"'"}'
run_case "one_long_str_56"        0 1  "[$LONG_STR_56]"                                            || FAILED=1
run_case "one_long_str_300"       0 1  "[$LONG_STR_300]"                                           || FAILED=1
# Short sub-list
run_case "nested_short_list"      0 2  "[[1, 2], [3, 4, 5]]"                                       || FAILED=1
# Access-list shape (used by EIP-2930+ txs): 2 entries
ACCESS_LIST="[[$ALICE, [$SLOT1, $SLOT2]], [$BOB, [$SLOT1]]]"
run_case "access_list_2_entries"  0 2  "$ACCESS_LIST"                                              || FAILED=1
# 6 blob versioned hashes (Cancun max), each 32B
BLOB_HASH='{"hex": "01aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"}'
run_case "blob_hashes_6"          0 6  "[$BLOB_HASH, $BLOB_HASH, $BLOB_HASH, $BLOB_HASH, $BLOB_HASH, $BLOB_HASH]" || FAILED=1
# Authorization-list shape: 3 entries of [chain_id, address, nonce, y_parity, r, s]
SIG='{"hex": "1111111111111111111111111111111111111111111111111111111111111111"}'
AUTH_ENTRY="[1, $ALICE, 0, 0, $SIG, $SIG]"
run_case "auth_list_3_entries"    0 3  "[$AUTH_ENTRY, $AUTH_ENTRY, $AUTH_ENTRY]"                   || FAILED=1
# Many items (long outer list)
MANY_ITEMS="$(python3 -c "import sys; sys.stdout.write('['+', '.join([str(i & 0x7f) for i in range(100)])+']')")"
run_case "long_outer_list_100"    0 100 "$MANY_ITEMS"                                              || FAILED=1
# Failure: not a list (single byte string)
# Cannot easily construct via RLP encoder; manually write a non-list RLP byte:
NON_LIST_FILE="$REPO_ROOT/gen-out/zisk_rlp_list_count_items_non_list.input"
python3 -c "
import struct, sys
# Single byte 0x80 = empty string (not a list)
b = bytes([0x80])
with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(b)))
    f.write(b)
    f.write(b'\x00' * 7)
" "$NON_LIST_FILE"
"$ZISKEMU" -e gen-out/zisk_rlp_list_count_items.elf \
  -i "$NON_LIST_FILE" -o "$REPO_ROOT/gen-out/zisk_rlp_list_count_items_non_list.output" -n 500000 \
  >"$REPO_ROOT/gen-out/zisk_rlp_list_count_items_non_list.emu.log" 2>&1 || true
NL_STATUS="$(xxd -p -l 8 "$REPO_ROOT/gen-out/zisk_rlp_list_count_items_non_list.output" | tr -d '\n')"
NL_COUNT="$(dd if="$REPO_ROOT/gen-out/zisk_rlp_list_count_items_non_list.output" bs=1 skip=8 count=8 2>/dev/null | xxd -p | tr -d '\n')"
if [[ "$NL_STATUS" == "0100000000000000" && "$NL_COUNT" == "0000000000000000" ]]; then
  printf "  %-30s OK   status=1 count=0 (non-list rejected)\n" "non_list_rejected"
else
  printf "  %-30s FAIL  status=0x%s count=0x%s\n" "non_list_rejected" "$NL_STATUS" "$NL_COUNT"
  FAILED=1
fi

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: rlp_list_count_items walks every RLP item shape"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
