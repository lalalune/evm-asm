#!/usr/bin/env bash
# codegen-zisk-u256-eq-check.sh -- PR-K53.
#
# Equality predicate on 32-byte BE u256 buffers. Companion
# to PR-K50 u256_lt.
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

echo "==> emit zisk_u256_eq ELF"
lake exe codegen --program zisk_u256_eq --halt linux93 \
  -o gen-out/zisk_u256_eq

REPO_ROOT="$(pwd)"

# run_case <name> <a_dec> <b_dec> <expected_eq 0|1>
run_case() {
  local name="$1" a="$2" b="$3" expected="$4"

  local in_file="$REPO_ROOT/gen-out/zisk_u256_eq_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_u256_eq_${name}.output"

  python3 -c "
import sys
a = $a
b = $b
out  = a.to_bytes(32, 'big')
out += b.to_bytes(32, 'big')
sys.stdout.buffer.write(out)
" > "$in_file"

  "$ZISKEMU" -e gen-out/zisk_u256_eq.elf \
    -i "$in_file" -o "$out_file" -n 500000 \
    >"$REPO_ROOT/gen-out/zisk_u256_eq_${name}.emu.log" 2>&1 || true

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

MAX=115792089237316195423570985008687907853269984665640564039457584007913129639935
H64=$(python3 -c "print(1 << 64)")
H128=$(python3 -c "print(1 << 128)")
H192=$(python3 -c "print(1 << 192)")
H255=$(python3 -c "print(1 << 255)")

FAILED=0
# Equality
run_case "zero_eq_zero"          0           0           1   || FAILED=1
run_case "one_eq_one"            1           1           1   || FAILED=1
run_case "max_eq_max"            "$MAX"      "$MAX"      1   || FAILED=1
run_case "h128_eq_h128"          "$H128"     "$H128"     1   || FAILED=1
run_case "h255_eq_h255"          "$H255"     "$H255"     1   || FAILED=1
# Inequality
run_case "zero_neq_one"          0           1           0   || FAILED=1
run_case "one_neq_zero"          1           0           0   || FAILED=1
run_case "zero_neq_max"          0           "$MAX"      0   || FAILED=1
run_case "max_neq_zero"          "$MAX"      0           0   || FAILED=1
# MSB-only diff (first byte)
A_TOP=$(python3 -c "print(0x10 << (31*8))")
B_TOP=$(python3 -c "print(0x20 << (31*8))")
run_case "top_byte_neq"          "$A_TOP"    "$B_TOP"    0   || FAILED=1
# LSB-only diff (last byte)
run_case "low_byte_neq"          0           1           0   || FAILED=1
# Mid-byte diff
A_MID=$(python3 -c "print(1 << 80)")
B_MID=$(python3 -c "print((1 << 80) + 1)")
run_case "mid_byte_neq"          "$A_MID"    "$B_MID"    0   || FAILED=1
# Near-equal at every byte boundary
run_case "max_neq_max_minus_1"   "$MAX"      $(python3 -c "print((1<<256)-2)")  0   || FAILED=1
# 2^255 vs 2^255-1
run_case "h255_neq_h255_minus_1" "$H255"     $(python3 -c "print((1<<255)-1)")  0   || FAILED=1
# Identical mid-magnitude
ONE_ETH=$(python3 -c "print(10**18)")
run_case "one_eth_eq_one_eth"    "$ONE_ETH"  "$ONE_ETH"  1   || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: u256_eq matches Python's == for 15 fixtures"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
