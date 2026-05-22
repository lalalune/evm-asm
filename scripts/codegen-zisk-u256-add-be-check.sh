#!/usr/bin/env bash
# codegen-zisk-u256-add-be-check.sh -- PR-K51.
#
# Modular addition on 32-byte big-endian u256 buffers, with
# overflow flag.
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

echo "==> emit zisk_u256_add_be ELF"
lake exe codegen --program zisk_u256_add_be --halt linux93 \
  -o gen-out/zisk_u256_add_be

REPO_ROOT="$(pwd)"

# run_case <name> <a_dec> <b_dec>
run_case() {
  local name="$1" a="$2" b="$3"

  local in_file="$REPO_ROOT/gen-out/zisk_u256_add_be_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_u256_add_be_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_u256_add_be_${name}.expected"

  python3 -c "
import struct, sys
a = $a
b = $b
MOD = 1 << 256
total = a + b
overflow = 1 if total >= MOD else 0
result = total % MOD

with open(sys.argv[1], 'wb') as f:
    f.write(a.to_bytes(32, 'big'))
    f.write(b.to_bytes(32, 'big'))

with open(sys.argv[2], 'wb') as f:
    f.write(struct.pack('<Q', overflow))
    f.write(result.to_bytes(32, 'big'))
" "$in_file" "$exp_file"

  "$ZISKEMU" -e gen-out/zisk_u256_add_be.elf \
    -i "$in_file" -o "$out_file" -n 500000 \
    >"$REPO_ROOT/gen-out/zisk_u256_add_be_${name}.emu.log" 2>&1 || true

  local exp_size; exp_size="$(stat -c%s "$exp_file")"
  local actual expected
  actual="$(xxd -p -l "$exp_size" "$out_file" 2>/dev/null | tr -d '\n')"
  expected="$(xxd -p -l "$exp_size" "$exp_file" 2>/dev/null | tr -d '\n')"

  if [[ "$actual" == "$expected" ]]; then
    local of; of="$(python3 -c "print(1 if ($a + $b) >= (1<<256) else 0)")"
    printf "  %-30s OK   overflow=%d\n" "$name" "$of"
    return 0
  else
    printf "  %-30s FAIL\n    expected: %s\n    actual:   %s\n" \
      "$name" "$expected" "$actual"
    return 1
  fi
}

ONE=1
MAX=115792089237316195423570985008687907853269984665640564039457584007913129639935
H64=$(python3 -c "print(1 << 64)")
H128=$(python3 -c "print(1 << 128)")
H192=$(python3 -c "print(1 << 192)")
H255=$(python3 -c "print(1 << 255)")
ONE_ETH=$(python3 -c "print(10**18)")
GAS_COST=$(python3 -c "print(21000 * 10**9)")

FAILED=0
# Identity
run_case "zero_plus_zero"        0            0            || FAILED=1
run_case "max_plus_zero"         "$MAX"       0            || FAILED=1
run_case "zero_plus_max"         0            "$MAX"       || FAILED=1
# Simple sums
run_case "one_plus_one"          1            1            || FAILED=1
run_case "100_plus_200"          100          200          || FAILED=1
# Carry across the 64-bit boundary
H64_MINUS_1=$(python3 -c "print((1<<64) - 1)")
run_case "carry_through_64"      "$H64_MINUS_1" 1          || FAILED=1
# Carry across the 128-bit boundary
H128_MINUS_1=$(python3 -c "print((1<<128) - 1)")
run_case "carry_through_128"     "$H128_MINUS_1" 1         || FAILED=1
# Carry across the 192-bit boundary
H192_MINUS_1=$(python3 -c "print((1<<192) - 1)")
run_case "carry_through_192"     "$H192_MINUS_1" 1         || FAILED=1
# Long carry chain (almost-max + 1)
run_case "max_plus_one"          "$MAX"       1            || FAILED=1
# Full overflow
run_case "max_plus_max"          "$MAX"       "$MAX"       || FAILED=1
# Just-below + just-below
H255_MINUS_1=$(python3 -c "print((1<<255) - 1)")
run_case "h255m1_plus_h255m1"    "$H255_MINUS_1" "$H255_MINUS_1" || FAILED=1
# H255 + H255 = 2^256 = overflow → result 0
run_case "h255_plus_h255"        "$H255"      "$H255"      || FAILED=1
# Realistic gas-cost addition
run_case "balance_plus_value"    "$ONE_ETH"   "$GAS_COST"  || FAILED=1
# H64 + H64 (no overflow)
run_case "h64_plus_h64"          "$H64"       "$H64"       || FAILED=1
# H192 + H192 (no overflow)
run_case "h192_plus_h192"        "$H192"      "$H192"      || FAILED=1
# 0xff byte at each position to cascade carry
ALT_PATTERN=$(python3 -c "print(int.from_bytes(b'\\xff' * 16 + b'\\x00' * 16, 'big'))")
run_case "high_half_max"         "$ALT_PATTERN" 0          || FAILED=1
run_case "high_half_plus_low"    "$ALT_PATTERN" 1          || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: u256_add_be matches Python's (a + b) mod 2^256 across 17 fixtures"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
