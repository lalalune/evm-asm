#!/usr/bin/env bash
# codegen-zisk-u256-div-u64-be-check.sh -- PR-K61.
#
# u256 / u64 long division on a BE buffer. b ≤ 2^56.
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

echo "==> emit zisk_u256_div_u64_be ELF"
lake exe codegen --program zisk_u256_div_u64_be --halt linux93 \
  -o gen-out/zisk_u256_div_u64_be

REPO_ROOT="$(pwd)"

# run_case <name> <a_dec> <b_dec>
run_case() {
  local name="$1" a="$2" b="$3"

  local in_file="$REPO_ROOT/gen-out/zisk_u256_div_u64_be_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_u256_div_u64_be_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_u256_div_u64_be_${name}.expected"

  python3 -c "
import struct, sys
a = $a
b = $b
with open(sys.argv[1], 'wb') as f:
    f.write(a.to_bytes(32, 'big'))
    f.write(struct.pack('<Q', b))

q, r = divmod(a, b)
with open(sys.argv[2], 'wb') as f:
    f.write(struct.pack('<Q', r))
    f.write(q.to_bytes(32, 'big'))
" "$in_file" "$exp_file"

  "$ZISKEMU" -e gen-out/zisk_u256_div_u64_be.elf \
    -i "$in_file" -o "$out_file" -n 500000 \
    >"$REPO_ROOT/gen-out/zisk_u256_div_u64_be_${name}.emu.log" 2>&1 || true

  local exp_size; exp_size="$(stat -c%s "$exp_file")"
  local actual expected
  actual="$(xxd -p -l "$exp_size" "$out_file" 2>/dev/null | tr -d '\n')"
  expected="$(xxd -p -l "$exp_size" "$exp_file" 2>/dev/null | tr -d '\n')"

  if [[ "$actual" == "$expected" ]]; then
    local q r; q="$(python3 -c "print($a // $b)")"; r="$(python3 -c "print($a % $b)")"
    printf "  %-30s OK   q=%s r=%d\n" "$name" "${q:0:16}..." "$r"
    return 0
  else
    printf "  %-30s FAIL\n    expected: %s\n    actual:   %s\n" \
      "$name" "$expected" "$actual"
    return 1
  fi
}

MAX256=115792089237316195423570985008687907853269984665640564039457584007913129639935
ONE_ETH=$(python3 -c "print(10**18)")
H40=$(python3 -c "print(1 << 40)")
H56=$(python3 -c "print(1 << 56)")  # Max allowed b

FAILED=0
# Divide by 1: q = a, r = 0
run_case "div_by_one"            "$MAX256"  1          || FAILED=1
run_case "div_by_one_zero"       0          1          || FAILED=1
# Divide by 2 (gas_target denominator)
run_case "div_by_two_max"        "$MAX256"  2          || FAILED=1
run_case "div_by_two_odd"        $(python3 -c "print((1<<256) - 1)")  2  || FAILED=1
run_case "div_by_two_eth"        "$ONE_ETH" 2          || FAILED=1
# Divide by 8 (BASE_FEE_MAX_CHANGE_DENOMINATOR)
run_case "div_by_eight"          "$ONE_ETH" 8          || FAILED=1
run_case "div_by_eight_max"      "$MAX256"  8          || FAILED=1
# Realistic EIP-1559 base-fee step
GAS_LIMIT=30000000
PARENT_GAS_TARGET=15000000
run_case "div_by_gas_target"     $(python3 -c "print(100 * 10**9 * 1000000)")  "$PARENT_GAS_TARGET"  || FAILED=1
# Divide-equal cases
run_case "div_a_eq_b"            $(python3 -c "print(1 << 30)")  $(python3 -c "print(1 << 30)") || FAILED=1
# Small-magnitude
run_case "100_div_7"             100        7          || FAILED=1
run_case "999_div_1000"          999        1000       || FAILED=1  # q = 0, r = 999
# Boundary: divisor = max allowed (2^56)
run_case "div_by_2_56_max"       "$MAX256"  "$H56"     || FAILED=1
run_case "div_by_2_56_eth"       "$ONE_ETH" "$H56"     || FAILED=1
# Mid-range divisor (2^40)
run_case "div_by_2_40"           "$MAX256"  "$H40"     || FAILED=1
# Realistic mainnet shape: 1 ETH / 100 gwei  ≈ 10M
run_case "eth_div_100gwei"       "$ONE_ETH" $(python3 -c "print(100 * 10**9)") || FAILED=1
# Pseudo-random
PSEUDO=$(python3 -c "print(int.from_bytes(bytes((i*7+3) & 0xff for i in range(32)), 'big'))")
run_case "pseudo_div_31337"      "$PSEUDO"  31337      || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: u256_div_u64_be matches Python's divmod() across 16 fixtures"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
