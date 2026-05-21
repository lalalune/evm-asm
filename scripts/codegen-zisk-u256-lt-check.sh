#!/usr/bin/env bash
# codegen-zisk-u256-lt-check.sh -- PR-K50.
#
# Strict less-than comparison on 32-byte BE u256 buffers.
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

echo "==> emit zisk_u256_lt ELF"
lake exe codegen --program zisk_u256_lt --halt linux93 \
  -o gen-out/zisk_u256_lt

REPO_ROOT="$(pwd)"

# run_case <name> <a_dec> <b_dec> <expected_a_lt_b 0|1>
run_case() {
  local name="$1" a="$2" b="$3" expected="$4"

  local in_file="$REPO_ROOT/gen-out/zisk_u256_lt_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_u256_lt_${name}.output"

  python3 -c "
import sys
a = $a
b = $b
out  = a.to_bytes(32, 'big')
out += b.to_bytes(32, 'big')
sys.stdout.buffer.write(out)
" > "$in_file"

  "$ZISKEMU" -e gen-out/zisk_u256_lt.elf \
    -i "$in_file" -o "$out_file" -n 500000 \
    >"$REPO_ROOT/gen-out/zisk_u256_lt_${name}.emu.log" 2>&1 || true

  local actual; actual="$(xxd -p -l 8 "$out_file" 2>/dev/null | tr -d '\n')"
  local exp_le; exp_le="$(python3 -c "print(int('$expected').to_bytes(8, 'little').hex())")"

  if [[ "$actual" == "$exp_le" ]]; then
    printf "  %-30s OK   result=%d\n" "$name" "$expected"
    return 0
  else
    printf "  %-30s FAIL  expected %d got 0x%s\n" "$name" "$expected" "$actual"
    return 1
  fi
}

# Constants
ZERO=0
ONE=1
MAX=115792089237316195423570985008687907853269984665640564039457584007913129639935  # 2^256 - 1
# 1 << 128
H128=$(python3 -c "print(1 << 128)")
# 1 << 255
H255=$(python3 -c "print(1 << 255)")
# Some "typical" balance and gas-cost-like values (u256 wide)
ONE_ETH=$(python3 -c "print(10**18)")
GAS_COST=$(python3 -c "print(21000 * 10**9)")  # 21k gas at 1 gwei = 2.1e13

FAILED=0
# Equalities → not strictly less
run_case "zero_eq_zero"       0      0      0  || FAILED=1
run_case "one_eq_one"         1      1      0  || FAILED=1
run_case "max_eq_max"         "$MAX" "$MAX"  0  || FAILED=1
run_case "h255_eq_h255"       "$H255" "$H255" 0  || FAILED=1
# Strict lessness — various magnitudes
run_case "zero_lt_one"        0       1     1  || FAILED=1
run_case "one_lt_two"         1       2     1  || FAILED=1
run_case "zero_lt_max"        0     "$MAX"  1  || FAILED=1
run_case "max_minus_1_lt_max" $(python3 -c "print((1<<256)-2)") "$MAX" 1  || FAILED=1
# Greater → not less
run_case "one_not_lt_zero"    1       0     0  || FAILED=1
run_case "max_not_lt_zero"    "$MAX"  0     0  || FAILED=1
run_case "max_not_lt_one"     "$MAX"  1     0  || FAILED=1
# MSB differs only (top byte)
A_TOP=$(python3 -c "print(0x10 << (31*8))")
B_TOP=$(python3 -c "print(0x20 << (31*8))")
run_case "top_byte_diff"      "$A_TOP" "$B_TOP" 1  || FAILED=1
# LSB differs only (low byte)
run_case "low_byte_diff"      0       1     1  || FAILED=1
# Mid-byte differs
A_MID=$(python3 -c "print(1 << 64)")
B_MID=$(python3 -c "print((1 << 64) + 1)")
run_case "mid_byte_diff"      "$A_MID" "$B_MID" 1  || FAILED=1
run_case "mid_byte_diff_rev"  "$B_MID" "$A_MID" 0  || FAILED=1
# Crossing the 128-bit boundary
run_case "below_h128_lt_h128" $(python3 -c "print((1<<128) - 1)") "$H128"  1  || FAILED=1
run_case "h128_not_lt_below"  "$H128" $(python3 -c "print((1<<128) - 1)")  0  || FAILED=1
# Typical balance vs cost
run_case "balance_gt_cost"    "$ONE_ETH" "$GAS_COST" 0  || FAILED=1  # 1 ETH > 21000 gwei
run_case "balance_eq_cost"    "$GAS_COST" "$GAS_COST" 0  || FAILED=1
run_case "balance_lt_cost"    "$GAS_COST" "$ONE_ETH"  1  || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: u256_lt matches Python's < for 20 fixtures"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
