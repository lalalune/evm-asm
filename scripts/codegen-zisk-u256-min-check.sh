#!/usr/bin/env bash
# codegen-zisk-u256-min-check.sh -- PR-K59.
#
# Minimum of two 32-byte BE u256 buffers.
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

echo "==> emit zisk_u256_min ELF"
lake exe codegen --program zisk_u256_min --halt linux93 \
  -o gen-out/zisk_u256_min

REPO_ROOT="$(pwd)"

# run_case <name> <a_dec> <b_dec>
run_case() {
  local name="$1" a="$2" b="$3"

  local in_file="$REPO_ROOT/gen-out/zisk_u256_min_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_u256_min_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_u256_min_${name}.expected"

  python3 -c "
import sys
a = $a
b = $b
out  = a.to_bytes(32, 'big')
out += b.to_bytes(32, 'big')
sys.stdout.buffer.write(out)
" > "$in_file"

  python3 -c "
import sys
a = $a
b = $b
mn = a if a <= b else b  # On equality, asm picks a; on inequality, the smaller.
sys.stdout.buffer.write(mn.to_bytes(32, 'big'))
" > "$exp_file"

  "$ZISKEMU" -e gen-out/zisk_u256_min.elf \
    -i "$in_file" -o "$out_file" -n 500000 \
    >"$REPO_ROOT/gen-out/zisk_u256_min_${name}.emu.log" 2>&1 || true

  local actual; actual="$(xxd -p -l 32 "$out_file" | tr -d '\n')"
  local expected; expected="$(xxd -p -l 32 "$exp_file" | tr -d '\n')"

  if [[ "$actual" == "$expected" ]]; then
    local mn; mn="$(python3 -c "print($a if $a <= $b else $b)")"
    printf "  %-30s OK   min=%s\n" "$name" "${mn:0:24}..."
    return 0
  else
    printf "  %-30s FAIL\n    expected: %s\n    actual:   %s\n" \
      "$name" "$expected" "$actual"
    return 1
  fi
}

MAX=115792089237316195423570985008687907853269984665640564039457584007913129639935
H64=$(python3 -c "print(1 << 64)")
H128=$(python3 -c "print(1 << 128)")
ONE_GWEI=$(python3 -c "print(10**9)")
HUNDRED_GWEI=$(python3 -c "print(100 * 10**9)")

FAILED=0
# Equality (asm picks a)
run_case "zero_eq_zero"          0       0       || FAILED=1
run_case "one_eq_one"            1       1       || FAILED=1
run_case "max_eq_max"            "$MAX"  "$MAX"  || FAILED=1
# Strict ordering: a < b
run_case "zero_lt_one"           0       1       || FAILED=1
run_case "one_lt_two"            1       2       || FAILED=1
run_case "zero_lt_max"           0       "$MAX"  || FAILED=1
# Strict ordering: a > b
run_case "one_gt_zero"           1       0       || FAILED=1
run_case "max_gt_zero"           "$MAX"  0       || FAILED=1
run_case "two_gt_one"            2       1       || FAILED=1
# MSB-only diff
A_TOP=$(python3 -c "print(0x10 << (31*8))")
B_TOP=$(python3 -c "print(0x20 << (31*8))")
run_case "msb_a_lt_b"            "$A_TOP" "$B_TOP" || FAILED=1
run_case "msb_a_gt_b"            "$B_TOP" "$A_TOP" || FAILED=1
# LSB-only diff
run_case "lsb_a_lt_b"            0       1        || FAILED=1
# Mid-byte diff
A_MID=$(python3 -c "print(1 << 80)")
B_MID=$(python3 -c "print((1 << 80) + 1)")
run_case "mid_a_lt_b"            "$A_MID" "$B_MID" || FAILED=1
# Realistic priority-fee scenario
run_case "priority_cap_below"    "$ONE_GWEI" "$HUNDRED_GWEI"   || FAILED=1   # max_priority < (max_fee - base) → use priority
run_case "priority_cap_above"    "$HUNDRED_GWEI" "$ONE_GWEI"   || FAILED=1   # surplus < max_priority → use surplus
run_case "priority_eq_surplus"   "$ONE_GWEI" "$ONE_GWEI"       || FAILED=1
# 128-bit boundary
run_case "h128_vs_h128m1"        "$H128" $(python3 -c "print((1<<128) - 1)") || FAILED=1
# Crossing 64-bit boundary
run_case "h64_vs_h64p1"          "$H64"  $(python3 -c "print((1<<64) + 1)")  || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: u256_min matches Python's min() across 18 fixtures"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
