#!/usr/bin/env bash
# codegen-zisk-effective-gas-price-eip1559-check.sh -- PR-K70.
#
# effective_gas_price = base_fee + min(max_priority, max_fee - base_fee)
#                     = min(max_fee, base_fee + max_priority)
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

echo "==> emit zisk_effective_gas_price_eip1559 ELF"
lake exe codegen --program zisk_effective_gas_price_eip1559 --halt linux93 \
  -o gen-out/zisk_effective_gas_price_eip1559

REPO_ROOT="$(pwd)"

# run_case <name> <max_priority> <max_fee> <base_fee>
run_case() {
  local name="$1" mp="$2" mf="$3" bf="$4"

  local in_file="$REPO_ROOT/gen-out/zisk_effective_gas_price_eip1559_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_effective_gas_price_eip1559_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_effective_gas_price_eip1559_${name}.expected"

  python3 -c "
import struct, sys
mp = $mp; mf = $mf; bf = $bf
with open(sys.argv[1], 'wb') as f:
    f.write(mp.to_bytes(32, 'big'))
    f.write(mf.to_bytes(32, 'big'))
    f.write(bf.to_bytes(32, 'big'))

if mf < bf:
    status = 1
    egp = 0  # caller ignores; we don't constrain
else:
    status = 0
    surplus = mf - bf
    priority = min(mp, surplus)
    egp = bf + priority

with open(sys.argv[2], 'wb') as f:
    f.write(struct.pack('<Q', status))
    f.write(egp.to_bytes(32, 'big'))
" "$in_file" "$exp_file"

  "$ZISKEMU" -e gen-out/zisk_effective_gas_price_eip1559.elf \
    -i "$in_file" -o "$out_file" -n 500000 \
    >"$REPO_ROOT/gen-out/zisk_effective_gas_price_eip1559_${name}.emu.log" 2>&1 || true

  # For reject path, only compare status (the out bytes are ignored)
  local exp_status; exp_status="$(python3 -c "print(1 if $mf < $bf else 0)")"
  local actual_status; actual_status="$(xxd -p -l 8 "$out_file" | tr -d '\n')"
  local exp_status_le; exp_status_le="$(python3 -c "print(int('$exp_status').to_bytes(8, 'little').hex())")"

  if [[ "$actual_status" != "$exp_status_le" ]]; then
    printf "  %-30s FAIL  status expected %d got 0x%s\n" "$name" "$exp_status" "$actual_status"
    return 1
  fi

  if [[ "$exp_status" == "1" ]]; then
    printf "  %-30s OK   status=1 (reject)\n" "$name"
    return 0
  fi

  # Pass path: compare full 40-byte output
  local actual expected
  actual="$(xxd -p -l 40 "$out_file" | tr -d '\n')"
  expected="$(xxd -p -l 40 "$exp_file" | tr -d '\n')"
  if [[ "$actual" == "$expected" ]]; then
    local egp; egp="$(python3 -c "print($bf + min($mp, $mf - $bf))")"
    printf "  %-30s OK   status=0 egp=%s\n" "$name" "$egp"
    return 0
  else
    printf "  %-30s FAIL  egp mismatch\n    expected: %s\n    actual:   %s\n" "$name" "$expected" "$actual"
    return 1
  fi
}

GWEI=$(python3 -c "print(10**9)")
ETH=$(python3 -c "print(10**18)")

FAILED=0
# Common scenarios
# 1) max_priority caps; egp = base + max_priority
run_case "priority_caps_egp"  $(python3 -c "print(2 * $GWEI)") $(python3 -c "print(100 * $GWEI)") $(python3 -c "print(50 * $GWEI)") || FAILED=1
# 2) surplus caps; egp = max_fee
run_case "surplus_caps_egp"   $(python3 -c "print(100 * $GWEI)") $(python3 -c "print(55 * $GWEI)") $(python3 -c "print(50 * $GWEI)") || FAILED=1
# 3) equal max_priority and surplus
run_case "equal_priority_surplus" $(python3 -c "print(10 * $GWEI)") $(python3 -c "print(60 * $GWEI)") $(python3 -c "print(50 * $GWEI)") || FAILED=1
# 4) max_fee == base_fee → priority = 0 → egp = base_fee
run_case "zero_surplus_egp_eq_base" $(python3 -c "print(5 * $GWEI)") $(python3 -c "print(50 * $GWEI)") $(python3 -c "print(50 * $GWEI)") || FAILED=1
# 5) max_priority == 0 → egp = base
run_case "zero_priority_egp_eq_base" 0 $(python3 -c "print(50 * $GWEI)") $(python3 -c "print(50 * $GWEI)") || FAILED=1
# 6) Reject: max_fee < base_fee
run_case "reject_max_fee_below_base" $(python3 -c "print(5 * $GWEI)") $(python3 -c "print(40 * $GWEI)") $(python3 -c "print(50 * $GWEI)") || FAILED=1
# 7) base_fee = 0, priority caps
run_case "zero_base_priority_caps"   $(python3 -c "print(5 * $GWEI)") $(python3 -c "print(50 * $GWEI)") 0 || FAILED=1
# 8) base_fee = 0, surplus caps
run_case "zero_base_surplus_caps"    $(python3 -c "print(50 * $GWEI)") $(python3 -c "print(5 * $GWEI)") 0 || FAILED=1
# 9) Realistic Holesky shape
run_case "holesky_typical"           $(python3 -c "print(3 * $GWEI)") $(python3 -c "print(35 * $GWEI)") $(python3 -c "print(8 * $GWEI)") || FAILED=1
# 10) Large u256 values
MAX=115792089237316195423570985008687907853269984665640564039457584007913129639935
run_case "max_priority_huge_zero_base" "$MAX" "$MAX" 0 || FAILED=1
# 11) Cross u128 boundary
H128=$(python3 -c "print(1 << 128)")
run_case "h128_boundary"             "$H128" $(python3 -c "print((1 << 128) + 1000)") 999 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: effective_gas_price_eip1559 matches base + min(max_priority, max_fee - base)"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
