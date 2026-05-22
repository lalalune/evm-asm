#!/usr/bin/env bash
# codegen-zisk-withdrawals-sum-amounts-check.sh -- PR-K65.
#
# Sum amount fields across an RLP list of Withdrawal records.
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

echo "==> emit zisk_withdrawals_sum_amounts ELF"
lake exe codegen --program zisk_withdrawals_sum_amounts --halt linux93 \
  -o gen-out/zisk_withdrawals_sum_amounts

REPO_ROOT="$(pwd)"

# run_case <name> <withdrawals_json>
#   withdrawals_json: list of [index, validator_idx, address_hex, amount] tuples.
run_case() {
  local name="$1" withdrawals_json="$2"

  local in_file="$REPO_ROOT/gen-out/zisk_withdrawals_sum_amounts_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_withdrawals_sum_amounts_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import json, struct, sys
import rlp

raw = json.loads('''$withdrawals_json''')
ws = []
for entry in raw:
    idx, vi, addr_hex, amt = entry
    ws.append([idx, vi, bytes.fromhex(addr_hex), amt])

rlp_bytes = rlp.encode(ws)
with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(rlp_bytes)))
    f.write(rlp_bytes)
    pad = (-(8 + len(rlp_bytes))) % 8
    if pad:
        f.write(b'\x00' * pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_withdrawals_sum_amounts.elf \
    -i "$in_file" -o "$out_file" -n 1000000 \
    >"$REPO_ROOT/gen-out/zisk_withdrawals_sum_amounts_${name}.emu.log" 2>&1 || true

  local actual_status; actual_status="$(xxd -p -l 8 "$out_file" | tr -d '\n')"
  local actual_sum;    actual_sum="$(dd if="$out_file" bs=1 skip=8 count=8 2>/dev/null | xxd -p | tr -d '\n')"

  local expected_sum; expected_sum="$(python3 -c "
import json
ws = json.loads('''$withdrawals_json''')
print(sum(w[3] for w in ws))
")"
  local expected_status=0
  local exp_status_le; exp_status_le="$(python3 -c "print(int('$expected_status').to_bytes(8, 'little').hex())")"
  local exp_sum_le; exp_sum_le="$(python3 -c "print(int('$expected_sum').to_bytes(8, 'little').hex())")"

  if [[ "$actual_status" == "$exp_status_le" && "$actual_sum" == "$exp_sum_le" ]]; then
    printf "  %-30s OK   status=0 sum=%d\n" "$name" "$expected_sum"
    return 0
  else
    printf "  %-30s FAIL  expected status=0 sum=%d, got status=0x%s sum=0x%s\n" \
      "$name" "$expected_sum" "$actual_status" "$actual_sum"
    return 1
  fi
}

ALICE="aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
BOB="bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"

FAILED=0
# Empty list
run_case "empty"           "[]"  || FAILED=1
# Single withdrawal
run_case "one_wd"          "[[0, 1, \"$ALICE\", 1000000000]]"  || FAILED=1
# Two withdrawals — typical magnitudes
run_case "two_wd_typical"  "[[10, 100, \"$ALICE\", 32000000000], [11, 101, \"$BOB\", 1500000000]]"  || FAILED=1
# Three withdrawals, mixed amounts
run_case "three_wd_mixed"  "[[1, 2, \"$ALICE\", 1], [2, 3, \"$BOB\", 1000000000], [3, 4, \"$ALICE\", 500000000]]"  || FAILED=1
# Six withdrawals
run_case "six_wd" "[[1, 1, \"$ALICE\", 100], [2, 2, \"$ALICE\", 200], [3, 3, \"$ALICE\", 300], [4, 4, \"$ALICE\", 400], [5, 5, \"$ALICE\", 500], [6, 6, \"$ALICE\", 600]]" || FAILED=1
# Mainnet-cap: 16 withdrawals
SIXTEEN_WD="$(python3 -c "
import sys
addr = '$ALICE'
ws = [[i, i+1000, addr, (i+1) * 1000000000] for i in range(16)]
import json
sys.stdout.write(json.dumps(ws))
")"
run_case "sixteen_wd_mainnet_cap" "$SIXTEEN_WD"  || FAILED=1
# Single max-u64 amount → sum equals it
run_case "max_amount_single"   "[[0, 0, \"$ALICE\", 18446744073709551615]]"  || FAILED=1
# Two max-u64 amounts → overflow → status=2
OVERFLOW_WD="[[0, 0, \"$ALICE\", 18446744073709551615], [1, 0, \"$BOB\", 1]]"
OVERFLOW_FILE="$REPO_ROOT/gen-out/zisk_withdrawals_sum_amounts_overflow.input"
uv run --directory execution-specs --quiet python3 -c "
import struct, sys, json, rlp
raw = json.loads('''$OVERFLOW_WD''')
ws = [[w[0], w[1], bytes.fromhex(w[2]), w[3]] for w in raw]
rlp_bytes = rlp.encode(ws)
with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(rlp_bytes)))
    f.write(rlp_bytes)
    pad = (-(8 + len(rlp_bytes))) % 8
    if pad:
        f.write(b'\x00' * pad)
" "$OVERFLOW_FILE"
"$ZISKEMU" -e gen-out/zisk_withdrawals_sum_amounts.elf \
  -i "$OVERFLOW_FILE" -o "$REPO_ROOT/gen-out/zisk_withdrawals_sum_amounts_overflow.output" \
  -n 1000000 >"$REPO_ROOT/gen-out/zisk_withdrawals_sum_amounts_overflow.emu.log" 2>&1 || true
OF_STATUS="$(xxd -p -l 8 "$REPO_ROOT/gen-out/zisk_withdrawals_sum_amounts_overflow.output" | tr -d '\n')"
if [[ "$OF_STATUS" == "0200000000000000" ]]; then
  printf "  %-30s OK   status=2 (overflow detected)\n" "overflow_detected"
else
  printf "  %-30s FAIL  status=0x%s\n" "overflow_detected" "$OF_STATUS"
  FAILED=1
fi
# Non-list input → status=1
NON_LIST_FILE="$REPO_ROOT/gen-out/zisk_withdrawals_sum_amounts_non_list.input"
python3 -c "
import struct, sys
b = bytes([0x80])
with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(b)))
    f.write(b)
    f.write(b'\x00' * 7)
" "$NON_LIST_FILE"
"$ZISKEMU" -e gen-out/zisk_withdrawals_sum_amounts.elf \
  -i "$NON_LIST_FILE" -o "$REPO_ROOT/gen-out/zisk_withdrawals_sum_amounts_non_list.output" \
  -n 1000000 >"$REPO_ROOT/gen-out/zisk_withdrawals_sum_amounts_non_list.emu.log" 2>&1 || true
NL_STATUS="$(xxd -p -l 8 "$REPO_ROOT/gen-out/zisk_withdrawals_sum_amounts_non_list.output" | tr -d '\n')"
if [[ "$NL_STATUS" == "0100000000000000" ]]; then
  printf "  %-30s OK   status=1 (non-list rejected)\n" "non_list_rejected"
else
  printf "  %-30s FAIL  status=0x%s\n" "non_list_rejected" "$NL_STATUS"
  FAILED=1
fi

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: withdrawals_sum_amounts matches Python's sum() with overflow detection"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
