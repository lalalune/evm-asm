#!/usr/bin/env bash
# codegen-zisk-access-list-count-check.sh -- PR-K48.
#
# Walk an EIP-2930+ access_list and return (num_addresses,
# num_storage_keys). Direct input to the intrinsic-gas formula.
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

echo "==> emit zisk_access_list_count ELF"
lake exe codegen --program zisk_access_list_count --halt linux93 \
  -o gen-out/zisk_access_list_count

REPO_ROOT="$(pwd)"

# run_case <name> <expected_status> <expected_num_addresses>
#         <expected_num_storage_keys> <access_list_json>
#
# access_list_json: list of [address_hex, [slot_hex, ...]] pairs.
run_case() {
  local name="$1" expected_status="$2" exp_addrs="$3" exp_slots="$4"
  local access_list_json="$5"

  local in_file="$REPO_ROOT/gen-out/zisk_access_list_count_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_access_list_count_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import json, struct, sys
import rlp

access_list_raw = json.loads('''$access_list_json''')
access_list = []
for entry in access_list_raw:
    addr_hex, slots_hex = entry
    addr = bytes.fromhex(addr_hex)
    slots = [bytes.fromhex(k) for k in slots_hex]
    access_list.append([addr, slots])

list_rlp = rlp.encode(access_list)
with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(list_rlp)))
    f.write(list_rlp)
    pad = (-(8 + len(list_rlp))) % 8
    if pad:
        f.write(b'\x00' * pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_access_list_count.elf \
    -i "$in_file" -o "$out_file" -n 500000 \
    >"$REPO_ROOT/gen-out/zisk_access_list_count_${name}.emu.log" 2>&1 || true

  local actual_status; actual_status="$(xxd -p -l 8 "$out_file" 2>/dev/null | tr -d '\n')"
  local actual_addrs; actual_addrs="$(dd if="$out_file" bs=1 skip=8 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local actual_slots; actual_slots="$(dd if="$out_file" bs=1 skip=16 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local exp_status_le; exp_status_le="$(python3 -c "print(int('$expected_status').to_bytes(8, 'little').hex())")"
  local exp_addrs_le;  exp_addrs_le="$(python3 -c "print(int('$exp_addrs').to_bytes(8, 'little').hex())")"
  local exp_slots_le;  exp_slots_le="$(python3 -c "print(int('$exp_slots').to_bytes(8, 'little').hex())")"

  if [[ "$actual_status" == "$exp_status_le" \
     && "$actual_addrs"  == "$exp_addrs_le" \
     && "$actual_slots"  == "$exp_slots_le" ]]; then
    printf "  %-30s OK   status=%d addrs=%d slots=%d\n" \
      "$name" "$expected_status" "$exp_addrs" "$exp_slots"
    return 0
  else
    printf "  %-30s FAIL  expected (%d, %d, %d) got (0x%s, 0x%s, 0x%s)\n" \
      "$name" "$expected_status" "$exp_addrs" "$exp_slots" \
      "$actual_status" "$actual_addrs" "$actual_slots"
    return 1
  fi
}

ALICE="aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
BOB="bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"
CAROL="cccccccccccccccccccccccccccccccccccccccc"
S1="5555555555555555555555555555555555555555555555555555555555555555"
S2="6666666666666666666666666666666666666666666666666666666666666666"
S3="7777777777777777777777777777777777777777777777777777777777777777"

FAILED=0
# Empty list
run_case "empty"                   0 0 0  "[]"                                                      || FAILED=1
# 1 address, no slots
run_case "one_addr_no_slots"       0 1 0  "[[\"$ALICE\", []]]"                                      || FAILED=1
# 1 address, 1 slot
run_case "one_addr_one_slot"       0 1 1  "[[\"$ALICE\", [\"$S1\"]]]"                              || FAILED=1
# 1 address, 3 slots
run_case "one_addr_three_slots"    0 1 3  "[[\"$ALICE\", [\"$S1\", \"$S2\", \"$S3\"]]]"            || FAILED=1
# 2 addresses, mixed slots
run_case "two_addrs_mixed_slots"   0 2 4  "[[\"$ALICE\", [\"$S1\", \"$S2\", \"$S3\"]], [\"$BOB\", [\"$S1\"]]]" || FAILED=1
# 3 addresses, all empty slots
run_case "three_addrs_no_slots"    0 3 0  "[[\"$ALICE\", []], [\"$BOB\", []], [\"$CAROL\", []]]"   || FAILED=1
# 3 addresses, total 6 slots
run_case "three_addrs_six_slots"   0 3 6  "[[\"$ALICE\", [\"$S1\", \"$S2\"]], [\"$BOB\", [\"$S1\", \"$S2\"]], [\"$CAROL\", [\"$S1\", \"$S2\"]]]" || FAILED=1
# Many addresses (10) with 1 slot each
ENTRY="[\"$ALICE\", [\"$S1\"]]"
TEN_ENTRIES="$(python3 -c "import sys; sys.stdout.write('[' + ', '.join(['''$ENTRY'''] * 10) + ']')")"
run_case "ten_addrs_one_slot_each" 0 10 10 "$TEN_ENTRIES"                                           || FAILED=1
# Long outer list (triggers long-list RLP prefix path):
# 50 addresses each with 1 slot. Total RLP > 56 bytes for outer.
FIFTY_ENTRIES="$(python3 -c "import sys; sys.stdout.write('[' + ', '.join(['''$ENTRY'''] * 50) + ']')")"
run_case "fifty_addrs_one_slot"    0 50 50 "$FIFTY_ENTRIES"                                         || FAILED=1
# Long inner slot list (>56 bytes triggers long-list path for inner)
LONG_SLOTS="$(python3 -c "
import json, sys
slot_hex = '$S1'
sys.stdout.write(json.dumps(['$ALICE', [slot_hex]*20]))
")"
run_case "one_addr_twenty_slots"   0 1 20 "[$LONG_SLOTS]"                                           || FAILED=1

# Failure: non-list outer
NON_LIST_FILE="$REPO_ROOT/gen-out/zisk_access_list_count_non_list.input"
python3 -c "
import struct, sys
b = bytes([0x80])
with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(b)))
    f.write(b)
    f.write(b'\x00' * 7)
" "$NON_LIST_FILE"
"$ZISKEMU" -e gen-out/zisk_access_list_count.elf \
  -i "$NON_LIST_FILE" -o "$REPO_ROOT/gen-out/zisk_access_list_count_non_list.output" -n 500000 \
  >"$REPO_ROOT/gen-out/zisk_access_list_count_non_list.emu.log" 2>&1 || true
NL_STATUS="$(xxd -p -l 8 "$REPO_ROOT/gen-out/zisk_access_list_count_non_list.output" | tr -d '\n')"
NL_ADDRS="$(dd if="$REPO_ROOT/gen-out/zisk_access_list_count_non_list.output" bs=1 skip=8 count=8 2>/dev/null | xxd -p | tr -d '\n')"
NL_SLOTS="$(dd if="$REPO_ROOT/gen-out/zisk_access_list_count_non_list.output" bs=1 skip=16 count=8 2>/dev/null | xxd -p | tr -d '\n')"
if [[ "$NL_STATUS" == "0100000000000000" && "$NL_ADDRS" == "0000000000000000" && "$NL_SLOTS" == "0000000000000000" ]]; then
  printf "  %-30s OK   status=1 (non-list rejected)\n" "non_list_rejected"
else
  printf "  %-30s FAIL  status=0x%s addrs=0x%s slots=0x%s\n" "non_list_rejected" "$NL_STATUS" "$NL_ADDRS" "$NL_SLOTS"
  FAILED=1
fi

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: access_list_count returns (num_addresses, num_storage_keys)"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
