#!/usr/bin/env bash
# codegen-zisk-block-withdrawals-total-check.sh -- PR-K85.
#
# Extract withdrawals from a block body and sum amounts.
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

echo "==> emit zisk_block_withdrawals_total ELF"
lake exe codegen --program zisk_block_withdrawals_total --halt linux93 \
  -o gen-out/zisk_block_withdrawals_total

REPO_ROOT="$(pwd)"

# run_case <name> <withdrawals_json>
run_case() {
  local name="$1" wds="$2"

  local in_file="$REPO_ROOT/gen-out/zisk_block_withdrawals_total_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_block_withdrawals_total_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import json, struct, sys, rlp
wds_raw = json.loads('''$wds''')
wds = []
for w in wds_raw:
    idx, vi, addr_hex, amt = w
    wds.append([idx, vi, bytes.fromhex(addr_hex), amt])
body = [[], [], wds]
body_rlp = rlp.encode(body)
with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(body_rlp)))
    f.write(body_rlp)
    pad = (-(8 + len(body_rlp))) % 8
    if pad: f.write(b'\x00' * pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_block_withdrawals_total.elf \
    -i "$in_file" -o "$out_file" -n 1000000 \
    >"$REPO_ROOT/gen-out/zisk_block_withdrawals_total_${name}.emu.log" 2>&1 || true

  local expected; expected="$(python3 -c "
import json
ws = json.loads('''$wds''')
print(sum(w[3] for w in ws))
")"
  local actual_status; actual_status="$(xxd -p -l 8 "$out_file" | tr -d '\n')"
  local actual_total;  actual_total="$(dd if="$out_file" bs=1 skip=8 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local exp_total_le;  exp_total_le="$(python3 -c "print(int('$expected').to_bytes(8, 'little').hex())")"

  if [[ "$actual_status" == "0000000000000000" && "$actual_total" == "$exp_total_le" ]]; then
    printf "  %-30s OK   total=%d\n" "$name" "$expected"
    return 0
  else
    printf "  %-30s FAIL  status=0x%s total=0x%s (expected %d)\n" "$name" "$actual_status" "$actual_total" "$expected"
    return 1
  fi
}

ALICE="aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"

FAILED=0
run_case "empty"              "[]"                                                    || FAILED=1
run_case "one_wd"             "[[0, 1, \"$ALICE\", 1000000000]]"                       || FAILED=1
run_case "three_wd" \
  "[[1, 1, \"$ALICE\", 100], [2, 2, \"$ALICE\", 200], [3, 3, \"$ALICE\", 300]]"        || FAILED=1
SIX_WD="$(python3 -c "
import json
addr = '$ALICE'
print(json.dumps([[i, i+1000, addr, (i+1) * 10**9] for i in range(6)]))
")"
run_case "six_wd"             "$SIX_WD"                                                || FAILED=1
SIXTEEN_WD="$(python3 -c "
import json
addr = '$ALICE'
print(json.dumps([[i, i+1000, addr, (i+1) * 10**9] for i in range(16)]))
")"
run_case "sixteen_wd"         "$SIXTEEN_WD"                                            || FAILED=1

# Body decode fail: 2-field body
TWO_FIELD_FILE="$REPO_ROOT/gen-out/zisk_block_withdrawals_total_two_field.input"
uv run --directory execution-specs --quiet python3 -c "
import struct, sys, rlp
body_rlp = rlp.encode([[], []])
with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(body_rlp)))
    f.write(body_rlp)
    pad = (-(8 + len(body_rlp))) % 8
    if pad: f.write(b'\x00' * pad)
" "$TWO_FIELD_FILE"
"$ZISKEMU" -e gen-out/zisk_block_withdrawals_total.elf \
  -i "$TWO_FIELD_FILE" -o "$REPO_ROOT/gen-out/zisk_block_withdrawals_total_two_field.output" \
  -n 500000 >"$REPO_ROOT/gen-out/zisk_block_withdrawals_total_two_field.emu.log" 2>&1 || true
TF_STATUS="$(xxd -p -l 8 "$REPO_ROOT/gen-out/zisk_block_withdrawals_total_two_field.output" | tr -d '\n')"
if [[ "$TF_STATUS" == "0100000000000000" ]]; then
  printf "  %-30s OK   status=1 (body decode fail)\n" "two_field_reject"
else
  printf "  %-30s FAIL  status=0x%s\n" "two_field_reject" "$TF_STATUS"
  FAILED=1
fi

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: block_withdrawals_total extracts withdrawals and sums amounts"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
