#!/usr/bin/env bash
# codegen-zisk-u256-to-u64-be-check.sh -- PR-K57.
#
# Truncate a 32-byte BE u256 buffer to u64 with overflow flag.
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

echo "==> emit zisk_u256_to_u64_be ELF"
lake exe codegen --program zisk_u256_to_u64_be --halt linux93 \
  -o gen-out/zisk_u256_to_u64_be

REPO_ROOT="$(pwd)"

# run_case <name> <value_dec>
run_case() {
  local name="$1" value="$2"

  local in_file="$REPO_ROOT/gen-out/zisk_u256_to_u64_be_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_u256_to_u64_be_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_u256_to_u64_be_${name}.expected"

  python3 -c "
import struct, sys
v = $value
sys.stdout.buffer.write(v.to_bytes(32, 'big'))  # u256 BE
" > "$in_file"

  python3 -c "
import struct, sys
v = $value
MOD = 1 << 64
overflow = 1 if v >= MOD else 0
low64 = v & (MOD - 1)
sys.stdout.buffer.write(struct.pack('<Q', overflow))
sys.stdout.buffer.write(struct.pack('<Q', low64))
" > "$exp_file"

  "$ZISKEMU" -e gen-out/zisk_u256_to_u64_be.elf \
    -i "$in_file" -o "$out_file" -n 500000 \
    >"$REPO_ROOT/gen-out/zisk_u256_to_u64_be_${name}.emu.log" 2>&1 || true

  local actual; actual="$(xxd -p -l 16 "$out_file" | tr -d '\n')"
  local expected; expected="$(xxd -p -l 16 "$exp_file" | tr -d '\n')"

  if [[ "$actual" == "$expected" ]]; then
    local of; of="$(python3 -c "print(1 if $value >= (1<<64) else 0)")"
    printf "  %-30s OK   overflow=%d low64=%d\n" "$name" "$of" $(($value & (2**64 - 1)))
    return 0
  else
    printf "  %-30s FAIL\n    expected: %s\n    actual:   %s\n" \
      "$name" "$expected" "$actual"
    return 1
  fi
}

MAX256=115792089237316195423570985008687907853269984665640564039457584007913129639935
MAX64=18446744073709551615
H64=$(python3 -c "print(1 << 64)")
H128=$(python3 -c "print(1 << 128)")
H192=$(python3 -c "print(1 << 192)")
H255=$(python3 -c "print(1 << 255)")

FAILED=0
# Fits in u64
run_case "zero"                  0          || FAILED=1
run_case "one"                   1          || FAILED=1
run_case "ff"                    255        || FAILED=1
run_case "0x100"                 256        || FAILED=1
run_case "two_to_32"             4294967296 || FAILED=1
run_case "two_to_56"             $(python3 -c "print(1 << 56)") || FAILED=1
run_case "two_to_63"             $(python3 -c "print(1 << 63)") || FAILED=1
run_case "max_u64_minus_1"       $(python3 -c "print((1 << 64) - 2)") || FAILED=1
run_case "max_u64"               "$MAX64"   || FAILED=1
# Overflows
run_case "two_to_64"             "$H64"     || FAILED=1
run_case "two_to_64_plus_1"      $(python3 -c "print((1 << 64) + 1)") || FAILED=1
run_case "two_to_128"            "$H128"    || FAILED=1
run_case "two_to_192"            "$H192"    || FAILED=1
run_case "two_to_255"            "$H255"    || FAILED=1
run_case "max_u256"              "$MAX256"  || FAILED=1
# Realistic: u128-shaped value (high bits set but only mid-magnitude)
run_case "tx_cost_typical"       $(python3 -c "print(100 * 10**9 * 30_000_000)") || FAILED=1
# Edge: only bit 64 set, low part 0
run_case "only_bit_64"           $(python3 -c "print(1 << 64)") || FAILED=1
# Pattern: low 64 = max, high 192 nonzero
run_case "pattern_high_set"      $(python3 -c "print((1 << 128) | ((1 << 64) - 1))") || FAILED=1
# Pattern: only some MSBs nonzero, low 64 = 0xdeadbeef
run_case "msbs_with_low_known"   $(python3 -c "print((1 << 200) | 0xdeadbeef)") || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: u256_to_u64_be truncates correctly and flags overflow"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
