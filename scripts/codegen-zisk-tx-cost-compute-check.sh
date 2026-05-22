#!/usr/bin/env bash
# codegen-zisk-tx-cost-compute-check.sh -- PR-K71.
#
# tx_cost = gas_limit × effective_gas_price + value
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

echo "==> emit zisk_tx_cost_compute ELF"
lake exe codegen --program zisk_tx_cost_compute --halt linux93 \
  -o gen-out/zisk_tx_cost_compute

REPO_ROOT="$(pwd)"

# run_case <name> <egp> <gas_limit> <value>
run_case() {
  local name="$1" egp="$2" gas="$3" value="$4"

  local in_file="$REPO_ROOT/gen-out/zisk_tx_cost_compute_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_tx_cost_compute_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_tx_cost_compute_${name}.expected"

  python3 -c "
import struct, sys
egp = $egp; gas = $gas; value = $value
with open(sys.argv[1], 'wb') as f:
    f.write(egp.to_bytes(32, 'big'))
    f.write(struct.pack('<Q', gas))
    f.write(value.to_bytes(32, 'big'))

MOD = 1 << 256
mul_overflow = (egp * gas) >= MOD
gas_fee = (egp * gas) % MOD
add_overflow = (gas_fee + value) >= MOD
tx_cost = (gas_fee + value) % MOD
status = 1 if (mul_overflow or add_overflow) else 0

with open(sys.argv[2], 'wb') as f:
    f.write(struct.pack('<Q', status))
    f.write(tx_cost.to_bytes(32, 'big'))
" "$in_file" "$exp_file"

  "$ZISKEMU" -e gen-out/zisk_tx_cost_compute.elf \
    -i "$in_file" -o "$out_file" -n 500000 \
    >"$REPO_ROOT/gen-out/zisk_tx_cost_compute_${name}.emu.log" 2>&1 || true

  local exp_status; exp_status="$(python3 -c "
egp, gas, value = $egp, $gas, $value
MOD = 1 << 256
print(1 if (egp * gas >= MOD) or ((egp * gas + value) >= MOD) else 0)
")"

  local actual_status; actual_status="$(xxd -p -l 8 "$out_file" | tr -d '\n')"
  local exp_status_le; exp_status_le="$(python3 -c "print(int('$exp_status').to_bytes(8, 'little').hex())")"

  if [[ "$actual_status" != "$exp_status_le" ]]; then
    printf "  %-30s FAIL  status expected %d got 0x%s\n" "$name" "$exp_status" "$actual_status"
    return 1
  fi

  if [[ "$exp_status" == "1" ]]; then
    printf "  %-30s OK   status=1 (overflow)\n" "$name"
    return 0
  fi

  # Pass: compare 40-byte output
  local actual expected
  actual="$(xxd -p -l 40 "$out_file" | tr -d '\n')"
  expected="$(xxd -p -l 40 "$exp_file" | tr -d '\n')"
  if [[ "$actual" == "$expected" ]]; then
    local cost; cost="$(python3 -c "print($egp * $gas + $value)")"
    printf "  %-30s OK   status=0 tx_cost=%s\n" "$name" "${cost:0:24}..."
    return 0
  else
    printf "  %-30s FAIL  cost mismatch\n    expected: %s\n    actual:   %s\n" "$name" "$expected" "$actual"
    return 1
  fi
}

GWEI=$(python3 -c "print(10**9)")
ETH=$(python3 -c "print(10**18)")

FAILED=0
# Typical mainnet transfer: 21000 × 50 gwei + 1 ETH
run_case "mainnet_transfer"   $(python3 -c "print(50 * $GWEI)")  21000  "$ETH"  || FAILED=1
# Contract creation: 100000 × 100 gwei + 0
run_case "creation_no_value"  $(python3 -c "print(100 * $GWEI)") 100000 0       || FAILED=1
# Zero gas → tx_cost = value
run_case "zero_gas"           $(python3 -c "print(100 * $GWEI)") 0      "$ETH"  || FAILED=1
# Zero value → tx_cost = gas × egp
run_case "zero_value"         $(python3 -c "print(50 * $GWEI)")  21000  0       || FAILED=1
# Zero egp → tx_cost = value
run_case "zero_egp"           0                                  21000  "$ETH"  || FAILED=1
# All zero
run_case "all_zero"           0                                  0      0       || FAILED=1
# Realistic high-fee: 30M gas × 100 gwei + 0
run_case "block_full_30M"     $(python3 -c "print(100 * $GWEI)") 30000000 0     || FAILED=1
# Overflow on mul: max egp × big gas
MAX=115792089237316195423570985008687907853269984665640564039457584007913129639935
run_case "mul_overflow"       "$MAX"                             2      0       || FAILED=1
# Overflow on add: max gas_fee + max value
run_case "add_overflow"       $(python3 -c "print(2**254)")      2      $(python3 -c "print(2**254)") || FAILED=1
# u128-bound egp (realistic)
H128=$(python3 -c "print((1 << 128) - 1)")
run_case "h128_egp_realistic" "$H128"                            30000000  "$ETH"  || FAILED=1
# Edge: gas = max u64
MAX_U64=18446744073709551615
run_case "max_u64_gas_one_egp" 1 "$MAX_U64" 0 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: tx_cost_compute matches Python's (egp × gas + value) mod 2^256"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
