#!/usr/bin/env bash
# codegen-zisk-u256-sub-be-check.sh -- PR-K52.
#
# Modular subtraction on 32-byte big-endian u256 buffers, with
# borrow (underflow) flag.
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

echo "==> emit zisk_u256_sub_be ELF"
lake exe codegen --program zisk_u256_sub_be --halt linux93 \
  -o gen-out/zisk_u256_sub_be

REPO_ROOT="$(pwd)"

# run_case <name> <a_dec> <b_dec>
run_case() {
  local name="$1" a="$2" b="$3"

  local in_file="$REPO_ROOT/gen-out/zisk_u256_sub_be_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_u256_sub_be_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_u256_sub_be_${name}.expected"

  python3 -c "
import struct, sys
a = $a
b = $b
MOD = 1 << 256
borrow = 1 if a < b else 0
result = (a - b) % MOD

with open(sys.argv[1], 'wb') as f:
    f.write(a.to_bytes(32, 'big'))
    f.write(b.to_bytes(32, 'big'))

with open(sys.argv[2], 'wb') as f:
    f.write(struct.pack('<Q', borrow))
    f.write(result.to_bytes(32, 'big'))
" "$in_file" "$exp_file"

  "$ZISKEMU" -e gen-out/zisk_u256_sub_be.elf \
    -i "$in_file" -o "$out_file" -n 500000 \
    >"$REPO_ROOT/gen-out/zisk_u256_sub_be_${name}.emu.log" 2>&1 || true

  local exp_size; exp_size="$(stat -c%s "$exp_file")"
  local actual expected
  actual="$(xxd -p -l "$exp_size" "$out_file" 2>/dev/null | tr -d '\n')"
  expected="$(xxd -p -l "$exp_size" "$exp_file" 2>/dev/null | tr -d '\n')"

  if [[ "$actual" == "$expected" ]]; then
    local b; b="$(python3 -c "print(1 if $a < $b else 0)")"
    printf "  %-30s OK   borrow=%d\n" "$name" "$b"
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
H192=$(python3 -c "print(1 << 192)")
H255=$(python3 -c "print(1 << 255)")
ONE_ETH=$(python3 -c "print(10**18)")
GAS_COST=$(python3 -c "print(21000 * 10**9)")

FAILED=0
# Identities
run_case "zero_minus_zero"       0       0       || FAILED=1
run_case "x_minus_x_max"         "$MAX"  "$MAX"  || FAILED=1
run_case "x_minus_zero"          "$MAX"  0       || FAILED=1
# Plain
run_case "one_minus_one"         1       1       || FAILED=1
run_case "two_minus_one"         2       1       || FAILED=1
run_case "200_minus_100"         200     100     || FAILED=1
# Underflow paths
run_case "zero_minus_one"        0       1       || FAILED=1   # all-1s, borrow=1
run_case "zero_minus_max"        0       "$MAX"  || FAILED=1   # = 1, borrow=1
run_case "one_minus_max"         1       "$MAX"  || FAILED=1
# Borrow propagation across boundaries
run_case "h64_minus_one"         "$H64"  1       || FAILED=1
run_case "h128_minus_one"        "$H128" 1       || FAILED=1
run_case "h192_minus_one"        "$H192" 1       || FAILED=1
run_case "h255_minus_one"        "$H255" 1       || FAILED=1
run_case "max_minus_one"         "$MAX"  1       || FAILED=1
# Underflow with borrow chain
H192_PLUS_1=$(python3 -c "print((1 << 192) + 1)")
run_case "h192_minus_h192p1"     "$H192" "$H192_PLUS_1"  || FAILED=1  # borrow
# Realistic tx-cost subtraction
run_case "balance_minus_cost_ok" "$ONE_ETH"  "$GAS_COST" || FAILED=1
run_case "balance_minus_cost_under" "$GAS_COST" "$ONE_ETH" || FAILED=1  # borrow
# Equal large values
H255M1=$(python3 -c "print((1 << 255) - 1)")
run_case "h255m1_minus_h255m1"   "$H255M1" "$H255M1"  || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: u256_sub_be matches Python's (a - b) mod 2^256 across 18 fixtures"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
