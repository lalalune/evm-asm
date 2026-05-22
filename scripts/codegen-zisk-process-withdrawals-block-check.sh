#!/usr/bin/env bash
# codegen-zisk-process-withdrawals-block-check.sh -- PR-K78.
#
# Iterate over a withdrawals RLP list and apply credits to a
# parallel pre-fetched balance array.
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

echo "==> emit zisk_process_withdrawals_block ELF"
lake exe codegen --program zisk_process_withdrawals_block --halt linux93 \
  -o gen-out/zisk_process_withdrawals_block

REPO_ROOT="$(pwd)"

# run_case <name> <withdrawals_json> <initial_balances_json>
#   withdrawals_json: list of [index, validator, addr_hex, amount_gwei]
#   initial_balances_json: list of u256 wei values (parallel to withdrawals)
run_case() {
  local name="$1" wds_json="$2" bals_json="$3"

  local in_file="$REPO_ROOT/gen-out/zisk_process_withdrawals_block_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_process_withdrawals_block_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_process_withdrawals_block_${name}.expected"

  uv run --directory execution-specs --quiet python3 -c "
import json, struct, sys
import rlp

wds_raw = json.loads('''$wds_json''')
bals    = json.loads('''$bals_json''')
assert len(wds_raw) == len(bals)

wds = []
for w in wds_raw:
    idx, vi, addr_hex, amt = w
    wds.append([idx, vi, bytes.fromhex(addr_hex), amt])

rlp_bytes = rlp.encode(wds)

# Build input file
out = struct.pack('<Q', len(wds))
for b in bals:
    out += b.to_bytes(32, 'big')
out += struct.pack('<Q', len(rlp_bytes))
out += rlp_bytes
pad = (-(len(out))) % 8
if pad:
    out += b'\x00' * pad

with open(sys.argv[1], 'wb') as f:
    f.write(out)

# Expected: status + balances after credits
new_bals = [b + wds_raw[i][3] * 10**9 for i, b in enumerate(bals)]
exp = struct.pack('<Q', 0)
for b in new_bals:
    exp += b.to_bytes(32, 'big')
with open(sys.argv[2], 'wb') as f:
    f.write(exp)
" "$in_file" "$exp_file"

  "$ZISKEMU" -e gen-out/zisk_process_withdrawals_block.elf \
    -i "$in_file" -o "$out_file" -n 1000000 \
    >"$REPO_ROOT/gen-out/zisk_process_withdrawals_block_${name}.emu.log" 2>&1 || true

  local exp_size; exp_size="$(stat -c%s "$exp_file")"
  local actual; actual="$(xxd -p -l "$exp_size" "$out_file" | tr -d '\n')"
  local expected; expected="$(xxd -p -l "$exp_size" "$exp_file" | tr -d '\n')"

  if [[ "$actual" == "$expected" ]]; then
    local n; n="$(python3 -c "import json; print(len(json.loads('''$wds_json''')))")"
    printf "  %-30s OK   n=%d\n" "$name" "$n"
    return 0
  else
    printf "  %-30s FAIL\n    expected: %s\n    actual:   %s\n" "$name" "$expected" "$actual"
    return 1
  fi
}

ALICE="aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
BOB="bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"
GWEI=$(python3 -c "print(10**9)")
ETH=$(python3 -c "print(10**18)")

FAILED=0
# Empty withdrawals (no balance changes, no entries to update)
run_case "empty"                "[]" "[]"  || FAILED=1
# Single withdrawal to zero balance
run_case "one_wd_zero_bal" \
  "[[0, 1, \"$ALICE\", $GWEI]]" \
  "[0]" || FAILED=1
# Single withdrawal to existing balance
run_case "one_wd_existing_bal" \
  "[[10, 100, \"$ALICE\", $(python3 -c "print(32 * 10**9)")]]" \
  "[$ETH]" || FAILED=1
# Two withdrawals
run_case "two_wd" \
  "[[1, 1, \"$ALICE\", 1000000000], [2, 2, \"$BOB\", 2000000000]]" \
  "[0, $ETH]" || FAILED=1
# Three withdrawals
run_case "three_wd" \
  "[[1, 1, \"$ALICE\", 100], [2, 2, \"$BOB\", 200], [3, 3, \"$ALICE\", 300]]" \
  "[0, $ETH, $(python3 -c "print(2 * 10**18)")]" || FAILED=1
# 6 withdrawals
run_case "six_wd" \
  "$(python3 -c "
import json
addr = '$ALICE'
ws = [[i, i+1000, addr, (i+1) * 10**8] for i in range(6)]
print(json.dumps(ws))
")" \
  "[0, 0, 0, 0, 0, 0]" || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: process_withdrawals_block credits all balances in parallel"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
