#!/usr/bin/env bash
# codegen-zisk-u256-is-zero-check.sh -- PR-K58.
#
# All-zero predicate on 32-byte u256 buffer.
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

echo "==> emit zisk_u256_is_zero ELF"
lake exe codegen --program zisk_u256_is_zero --halt linux93 \
  -o gen-out/zisk_u256_is_zero

REPO_ROOT="$(pwd)"

# run_case <name> <value_dec> <expected 0|1>
run_case() {
  local name="$1" value="$2" expected="$3"

  local in_file="$REPO_ROOT/gen-out/zisk_u256_is_zero_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_u256_is_zero_${name}.output"

  python3 -c "
import sys
v = $value
sys.stdout.buffer.write(v.to_bytes(32, 'big'))
" > "$in_file"

  "$ZISKEMU" -e gen-out/zisk_u256_is_zero.elf \
    -i "$in_file" -o "$out_file" -n 500000 \
    >"$REPO_ROOT/gen-out/zisk_u256_is_zero_${name}.emu.log" 2>&1 || true

  local actual; actual="$(xxd -p -l 8 "$out_file" | tr -d '\n')"
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

FAILED=0
# True
run_case "all_zero"              0          1   || FAILED=1
# False — pin one bit at each interesting position
run_case "lsb_set"               1          0   || FAILED=1
run_case "byte0_set_low"         255        0   || FAILED=1
run_case "byte1_set"             256        0   || FAILED=1
run_case "byte7_set"             $(python3 -c "print(1 << 56)") 0  || FAILED=1
run_case "byte8_set"             $(python3 -c "print(1 << 64)") 0  || FAILED=1
run_case "byte15_set"            $(python3 -c "print(1 << 120)") 0 || FAILED=1
run_case "byte16_set"            $(python3 -c "print(1 << 128)") 0 || FAILED=1
run_case "byte23_set"            $(python3 -c "print(1 << 184)") 0 || FAILED=1
run_case "byte24_set"            $(python3 -c "print(1 << 192)") 0 || FAILED=1
run_case "byte31_set"            $(python3 -c "print(1 << 248)") 0 || FAILED=1
run_case "msb_set"               $(python3 -c "print(1 << 255)") 0 || FAILED=1
run_case "max_u256"              "$MAX"     0   || FAILED=1
# Realistic
ONE_ETH=$(python3 -c "print(10**18)")
run_case "one_eth"               "$ONE_ETH" 0   || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: u256_is_zero detects all-zero buffer across all 32 byte positions"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
