#!/usr/bin/env bash
# codegen-zisk-validate-transaction-basic-check.sh -- PR-K76.
#
# Run the cheap u64-level tx-validation checks and verify the
# composite status code.
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

echo "==> emit zisk_validate_transaction_basic ELF"
lake exe codegen --program zisk_validate_transaction_basic --halt linux93 \
  -o gen-out/zisk_validate_transaction_basic

REPO_ROOT="$(pwd)"

# run_case <name> <expected_status>
#         <tx_chain> <block_chain> <tx_gas> <block_gas>
#         <tx_nonce> <account_nonce> <is_creation> <data_hex>
run_case() {
  local name="$1" expected_status="$2"
  local tx_chain="$3" block_chain="$4"
  local tx_gas="$5" block_gas="$6"
  local tx_nonce="$7" account_nonce="$8"
  local is_creation="$9" data_hex="${10}"

  local in_file="$REPO_ROOT/gen-out/zisk_validate_transaction_basic_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_validate_transaction_basic_${name}.output"

  python3 -c "
import struct, sys
data = bytes.fromhex('$data_hex')
out  = struct.pack('<Q', $tx_chain)
out += struct.pack('<Q', $block_chain)
out += struct.pack('<Q', $tx_gas)
out += struct.pack('<Q', $block_gas)
out += struct.pack('<Q', $tx_nonce)
out += struct.pack('<Q', $account_nonce)
out += struct.pack('<Q', $is_creation)
out += struct.pack('<Q', len(data))
out += data
pad = (-(72 + len(data))) % 8
if pad:
    out += b'\x00' * pad
sys.stdout.buffer.write(out)
" > "$in_file"

  "$ZISKEMU" -e gen-out/zisk_validate_transaction_basic.elf \
    -i "$in_file" -o "$out_file" -n 500000 \
    >"$REPO_ROOT/gen-out/zisk_validate_transaction_basic_${name}.emu.log" 2>&1 || true

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

FAILED=0
# All pass
run_case "all_pass_simple"      0   1 1 21000  30000000 5 5 0 ""               || FAILED=1
run_case "all_pass_with_data"   0   1 1 30000  30000000 0 0 0 "0011223344"     || FAILED=1
run_case "all_pass_creation"    0   1 1 100000 30000000 0 0 1 "6080604052"     || FAILED=1
# Step 1 fails (K69): chain_id, gas, or nonce — composite = 100 + sub
run_case "step1_chain_mismatch" 101 5 1 21000  30000000 5 5 0 ""               || FAILED=1
run_case "step1_gas_overshoot"  102 1 1 31000000 30000000 5 5 0 ""             || FAILED=1
run_case "step1_nonce_mismatch" 103 1 1 21000  30000000 5 6 0 ""               || FAILED=1
# Step 2 fails (K66): intrinsic_gas > tx.gas_limit — composite = 201
run_case "step2_intrinsic_over_call" 201 1 1 20999  30000000 5 5 0 ""          || FAILED=1
run_case "step2_intrinsic_over_creation" 201 1 1 52999 30000000 5 5 1 ""       || FAILED=1
run_case "step2_intrinsic_over_data" 201 1 1 21000 30000000 5 5 0 "ff"         || FAILED=1
# Boundary: intrinsic == gas_limit (pass)
run_case "boundary_gas_eq"      0   1 1 21000  30000000 5 5 0 ""               || FAILED=1
# Step 1 takes priority over step 2 (both would fail)
run_case "step1_priority_chain" 101 5 1 100    30000000 5 5 0 ""               || FAILED=1   # chain fail; gas also < 21000

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: validate_transaction_basic routes through K69 + K66 with composite codes"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
