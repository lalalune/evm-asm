#!/usr/bin/env bash
# codegen-zisk-u256-lt-be-check.sh -- PR-K160.
#
# Compare two 32-byte BE u256 buffers: return 1 if a < b, else 0.
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

echo "==> emit zisk_u256_lt_be ELF"
lake exe codegen --program zisk_u256_lt_be --halt linux93 \
  -o gen-out/zisk_u256_lt_be

REPO_ROOT="$(pwd)"

# run_case <name> <a_hex_32B> <b_hex_32B> <expected_is_less>
run_case() {
  local name="$1" a="$2" b="$3" exp="$4"

  local in_file="$REPO_ROOT/gen-out/zisk_u256_lt_be_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_u256_lt_be_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys
a = bytes.fromhex('$a')
b = bytes.fromhex('$b')
assert len(a) == 32 and len(b) == 32
with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', 0))
    f.write(a + b)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_u256_lt_be.elf \
    -i "$in_file" -o "$out_file" -n 100000 \
    >"$REPO_ROOT/gen-out/zisk_u256_lt_be_${name}.emu.log" 2>&1 || true

  local actual_status; actual_status="$(xxd -p -l 8 "$out_file" | tr -d '\n')"
  local actual_lt_le; actual_lt_le="$(dd if="$out_file" bs=1 skip=8 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local actual_lt; actual_lt="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$actual_lt_le'))[0])")"

  if [[ "$actual_status" == "0000000000000000" && "$actual_lt" == "$exp" ]]; then
    printf "  %-30s OK   is_less=%d\n" "$name" "$exp"
    return 0
  else
    printf "  %-30s FAIL status=0x%s is_less=%d expected=%d\n" "$name" "$actual_status" "$actual_lt" "$exp"
    return 1
  fi
}

zero() { python3 -c "print('00' * 32)"; }
one() { python3 -c "print('00' * 31 + '01')"; }
maxu() { python3 -c "print('ff' * 32)"; }
hi_byte() { python3 -c "print('01' + '00' * 31)"; }
mid() { python3 -c "print('00' * 16 + '01' + '00' * 15)"; }

FAILED=0
# Reflexive: a == a -> not less
run_case "zero_eq_zero"        "$(zero)"   "$(zero)"   0 || FAILED=1
run_case "max_eq_max"          "$(maxu)"   "$(maxu)"   0 || FAILED=1
run_case "one_eq_one"          "$(one)"    "$(one)"    0 || FAILED=1
# Strict ordering
run_case "zero_lt_one"         "$(zero)"   "$(one)"    1 || FAILED=1
run_case "one_lt_max"          "$(one)"    "$(maxu)"   1 || FAILED=1
run_case "zero_lt_max"         "$(zero)"   "$(maxu)"   1 || FAILED=1
# Greater (not less)
run_case "one_not_lt_zero"     "$(one)"    "$(zero)"   0 || FAILED=1
run_case "max_not_lt_zero"     "$(maxu)"   "$(zero)"   0 || FAILED=1
run_case "max_not_lt_one"      "$(maxu)"   "$(one)"    0 || FAILED=1
# MSB-driven decisions (the byte where they first differ is high)
run_case "msb_one_lt_msb_one"  "$(hi_byte)" "$(hi_byte)" 0 || FAILED=1
run_case "zero_lt_hi_byte"     "$(zero)"   "$(hi_byte)" 1 || FAILED=1
run_case "lo_byte_lt_hi_byte"  "$(one)"    "$(hi_byte)" 1 || FAILED=1
run_case "hi_byte_not_lt_max_no" "$(hi_byte)" "$(mid)"  0 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: u256_lt_be matches strict byte-BE comparison"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
