#!/usr/bin/env bash
# codegen-zisk-validate-transaction-balance-check.sh -- PR-K79.
#
# Verify sender.balance >= max_fee_per_gas × gas_limit + value.
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

echo "==> emit zisk_validate_transaction_balance ELF"
lake exe codegen --program zisk_validate_transaction_balance --halt linux93 \
  -o gen-out/zisk_validate_transaction_balance

REPO_ROOT="$(pwd)"

# run_case <name> <expected_status> <max_fee> <gas_limit> <value> <balance>
run_case() {
  local name="$1" expected_status="$2" mf="$3" gl="$4" val="$5" bal="$6"

  local in_file="$REPO_ROOT/gen-out/zisk_validate_transaction_balance_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_validate_transaction_balance_${name}.output"

  python3 -c "
import struct, sys
mf, gl, val, bal = $mf, $gl, $val, $bal
with open(sys.argv[1], 'wb') as f:
    f.write(mf.to_bytes(32, 'big'))
    f.write(struct.pack('<Q', gl))
    f.write(val.to_bytes(32, 'big'))
    f.write(bal.to_bytes(32, 'big'))
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_validate_transaction_balance.elf \
    -i "$in_file" -o "$out_file" -n 500000 \
    >"$REPO_ROOT/gen-out/zisk_validate_transaction_balance_${name}.emu.log" 2>&1 || true

  local actual; actual="$(xxd -p -l 8 "$out_file" | tr -d '\n')"
  local exp_le; exp_le="$(python3 -c "print(int('$expected_status').to_bytes(8, 'little').hex())")"

  if [[ "$actual" == "$exp_le" ]]; then
    printf "  %-30s OK   status=%d\n" "$name" "$expected_status"
    return 0
  else
    printf "  %-30s FAIL  expected status=%d got 0x%s\n" "$name" "$expected_status" "$actual"
    return 1
  fi
}

GWEI=$(python3 -c "print(10**9)")
ETH=$(python3 -c "print(10**18)")
MAX256=115792089237316195423570985008687907853269984665640564039457584007913129639935

FAILED=0
# Pass cases (balance >= cost)
run_case "simple_ok"            0 $(python3 -c "print(50 * $GWEI)") 21000 "$ETH" $(python3 -c "print(10**18 + 50 * 10**9 * 21000)") || FAILED=1
run_case "balance_eq_cost"      0 $(python3 -c "print(50 * $GWEI)") 21000 0 $(python3 -c "print(50 * $GWEI * 21000)") || FAILED=1
run_case "huge_balance"         0 $(python3 -c "print(50 * $GWEI)") 21000 "$ETH" "$MAX256" || FAILED=1
run_case "zero_cost_zero_bal"   0 0 0 0 0 || FAILED=1
run_case "zero_value_balance_ok" 0 $(python3 -c "print(100 * $GWEI)") 30000 0 "$ETH" || FAILED=1
# Reject (balance < cost)
run_case "balance_one_less"     2 $(python3 -c "print(50 * $GWEI)") 21000 0 $(python3 -c "print(50 * $GWEI * 21000 - 1)") || FAILED=1
run_case "zero_balance"         2 $(python3 -c "print(50 * $GWEI)") 21000 0 0 || FAILED=1
run_case "value_exceeds"        2 $(python3 -c "print(50 * $GWEI)") 21000 "$ETH" 1 || FAILED=1
# Overflow (cost computation overflows u256)
run_case "cost_mul_overflow"    1 "$MAX256" 2 0 "$ETH" || FAILED=1
# Realistic Holesky shape
run_case "holesky_ok" \
  0 $(python3 -c "print(8 * $GWEI)") 30000000 $(python3 -c "print(2 * 10**16)") "$ETH" || FAILED=1
# Realistic Holesky shape that should fail (balance too low)
run_case "holesky_insufficient" \
  2 $(python3 -c "print(8 * $GWEI)") 30000000 "$ETH" 1 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: validate_transaction_balance enforces balance >= max_fee*gas + value"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
