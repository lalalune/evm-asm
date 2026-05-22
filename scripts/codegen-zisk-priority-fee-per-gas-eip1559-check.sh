#!/usr/bin/env bash
# codegen-zisk-priority-fee-per-gas-eip1559-check.sh -- PR-K62.
#
# Compute the effective priority fee for an EIP-1559 tx:
#   surplus = max_fee - base_fee
#   priority_fee = min(max_priority, surplus)
# Returns 1 if max_fee < base_fee (caller should reject).
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

echo "==> emit zisk_priority_fee_per_gas_eip1559 ELF"
lake exe codegen --program zisk_priority_fee_per_gas_eip1559 --halt linux93 \
  -o gen-out/zisk_priority_fee_per_gas_eip1559

REPO_ROOT="$(pwd)"

# run_case <name> <max_priority> <max_fee> <base_fee>
run_case() {
  local name="$1" mp="$2" mf="$3" bf="$4"

  local in_file="$REPO_ROOT/gen-out/zisk_priority_fee_per_gas_eip1559_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_priority_fee_per_gas_eip1559_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_priority_fee_per_gas_eip1559_${name}.expected"

  python3 -c "
import struct, sys
mp = $mp; mf = $mf; bf = $bf
with open(sys.argv[1], 'wb') as f:
    f.write(mp.to_bytes(32, 'big'))
    f.write(mf.to_bytes(32, 'big'))
    f.write(bf.to_bytes(32, 'big'))

if mf < bf:
    status = 1
    pf = (mf - bf) % (1 << 256)  # underflow result; caller ignores
else:
    status = 0
    surplus = mf - bf
    pf = min(mp, surplus)

with open(sys.argv[2], 'wb') as f:
    f.write(struct.pack('<Q', status))
    f.write(pf.to_bytes(32, 'big'))
" "$in_file" "$exp_file"

  "$ZISKEMU" -e gen-out/zisk_priority_fee_per_gas_eip1559.elf \
    -i "$in_file" -o "$out_file" -n 500000 \
    >"$REPO_ROOT/gen-out/zisk_priority_fee_per_gas_eip1559_${name}.emu.log" 2>&1 || true

  local exp_size; exp_size="$(stat -c%s "$exp_file")"
  local actual expected
  actual="$(xxd -p -l "$exp_size" "$out_file" 2>/dev/null | tr -d '\n')"
  expected="$(xxd -p -l "$exp_size" "$exp_file" 2>/dev/null | tr -d '\n')"

  if [[ "$actual" == "$expected" ]]; then
    local status pf
    status="$(python3 -c "print(1 if $mf < $bf else 0)")"
    pf="$(python3 -c "
mp, mf, bf = $mp, $mf, $bf
if mf < bf: print('reject')
else:       print(min(mp, mf - bf))
")"
    printf "  %-30s OK   status=%d priority_fee=%s\n" "$name" "$status" "$pf"
    return 0
  else
    printf "  %-30s FAIL\n    expected: %s\n    actual:   %s\n" \
      "$name" "$expected" "$actual"
    return 1
  fi
}

GWEI=$(python3 -c "print(10**9)")
ETH=$(python3 -c "print(10**18)")

FAILED=0
# Surplus dominates → priority = max_priority
run_case "priority_below_surplus" \
  $(python3 -c "print(2 * $GWEI)")   $(python3 -c "print(100 * $GWEI)") $(python3 -c "print(50 * $GWEI)") \
  || FAILED=1

# max_priority caps the surplus → priority = max_priority (= 2 gwei)
run_case "priority_caps_surplus" \
  $(python3 -c "print(2 * $GWEI)")   $(python3 -c "print(100 * $GWEI)") $(python3 -c "print(50 * $GWEI)") \
  || FAILED=1

# Surplus is smaller than max_priority → priority = surplus
run_case "surplus_caps_priority" \
  $(python3 -c "print(100 * $GWEI)") $(python3 -c "print(55 * $GWEI)")  $(python3 -c "print(50 * $GWEI)") \
  || FAILED=1

# Exact equality of max_priority and surplus
run_case "equal_max_priority_surplus" \
  $(python3 -c "print(10 * $GWEI)")  $(python3 -c "print(60 * $GWEI)")  $(python3 -c "print(50 * $GWEI)") \
  || FAILED=1

# max_fee == base_fee → surplus = 0, priority = min(mp, 0) = 0
run_case "zero_surplus" \
  $(python3 -c "print(5 * $GWEI)")   $(python3 -c "print(50 * $GWEI)")  $(python3 -c "print(50 * $GWEI)") \
  || FAILED=1

# Reject: max_fee < base_fee
run_case "reject_max_fee_below_base" \
  $(python3 -c "print(5 * $GWEI)")   $(python3 -c "print(40 * $GWEI)")  $(python3 -c "print(50 * $GWEI)") \
  || FAILED=1

# Reject: max_fee = 0, base_fee > 0
run_case "reject_zero_max_fee" \
  0   0   "$GWEI" \
  || FAILED=1

# Edge: max_priority = 0 → priority = 0 (free tx)
run_case "zero_max_priority" \
  0   $(python3 -c "print(50 * $GWEI)") $(python3 -c "print(50 * $GWEI)") \
  || FAILED=1

# Realistic Holesky shape: large max_priority, modest surplus
run_case "holesky_typical" \
  $(python3 -c "print(3 * $GWEI)") $(python3 -c "print(35 * $GWEI)") $(python3 -c "print(8 * $GWEI)") \
  || FAILED=1

# Large u256 values (test the full byte-walk in u256_sub and u256_min)
MAX=115792089237316195423570985008687907853269984665640564039457584007913129639935
run_case "max_priority_huge" \
  "$MAX"  "$MAX"  0 \
  || FAILED=1

# Underflow chain across 64-bit boundary
H64=$(python3 -c "print(1 << 64)")
run_case "h64_minus_h64_plus_1" \
  $(python3 -c "print(2 * $GWEI)")  "$H64"  $(python3 -c "print((1<<64) + 1)") \
  || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: priority_fee_per_gas_eip1559 matches Python's min(max_priority, max_fee - base_fee)"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
