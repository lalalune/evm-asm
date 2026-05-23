#!/usr/bin/env bash
# codegen-zisk-bloom-eq-check.sh -- PR-K154.
#
# Byte-equal check between two 256-byte blooms.
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

echo "==> emit zisk_bloom_eq ELF"
lake exe codegen --program zisk_bloom_eq --halt linux93 \
  -o gen-out/zisk_bloom_eq

REPO_ROOT="$(pwd)"

# run_case <name> <bloom_a_hex> <bloom_b_hex> <expected_eq>
run_case() {
  local name="$1" a="$2" b="$3" exp="$4"

  local in_file="$REPO_ROOT/gen-out/zisk_bloom_eq_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_bloom_eq_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys
a = bytes.fromhex('$a')
b = bytes.fromhex('$b')
assert len(a) == 256 and len(b) == 256
with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', 0))
    f.write(a + b)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_bloom_eq.elf \
    -i "$in_file" -o "$out_file" -n 100000 \
    >"$REPO_ROOT/gen-out/zisk_bloom_eq_${name}.emu.log" 2>&1 || true

  local actual_status; actual_status="$(xxd -p -l 8 "$out_file" | tr -d '\n')"
  local actual_eq_le; actual_eq_le="$(dd if="$out_file" bs=1 skip=8 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local actual_eq; actual_eq="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$actual_eq_le'))[0])")"

  if [[ "$actual_status" == "0000000000000000" && "$actual_eq" == "$exp" ]]; then
    printf "  %-30s OK   is_equal=%d\n" "$name" "$exp"
    return 0
  else
    printf "  %-30s FAIL status=0x%s is_equal=%d expected=%d\n" "$name" "$actual_status" "$actual_eq" "$exp"
    return 1
  fi
}

ZERO="$(python3 -c "print('00' * 256)")"
ONES="$(python3 -c "print('ff' * 256)")"
RAND="$(python3 -c "import os; print(os.urandom(256).hex())")"
# Same as RAND but with one bit flipped in the last byte.
RAND_FLIP="$(python3 -c "import os; r=bytearray.fromhex('$RAND'); r[255] ^= 1; print(bytes(r).hex())")"
# Same as RAND but with one bit flipped in the first byte (different word).
RAND_FLIP_FIRST="$(python3 -c "r=bytearray.fromhex('$RAND'); r[0] ^= 0x80; print(bytes(r).hex())")"

FAILED=0
# Positive: both equal
run_case "zero_eq_zero"     "$ZERO" "$ZERO" 1 || FAILED=1
run_case "ones_eq_ones"     "$ONES" "$ONES" 1 || FAILED=1
run_case "random_eq_self"   "$RAND" "$RAND" 1 || FAILED=1
# Negative: differ
run_case "zero_neq_ones"    "$ZERO" "$ONES" 0 || FAILED=1
run_case "ones_neq_zero"    "$ONES" "$ZERO" 0 || FAILED=1
run_case "diff_last_byte"   "$RAND" "$RAND_FLIP" 0 || FAILED=1
run_case "diff_first_byte"  "$RAND" "$RAND_FLIP_FIRST" 0 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: bloom_eq distinguishes byte-equal from byte-differing 256-byte blooms"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
