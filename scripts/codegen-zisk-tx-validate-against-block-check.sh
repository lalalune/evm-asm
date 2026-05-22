#!/usr/bin/env bash
# codegen-zisk-tx-validate-against-block-check.sh -- PR-K69.
#
# Verify three cheap tx-validation invariants:
#   chain_id == block.chain_id
#   tx.gas_limit <= block.gas_limit
#   tx.nonce == account.nonce
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

echo "==> emit zisk_tx_validate_against_block ELF"
lake exe codegen --program zisk_tx_validate_against_block --halt linux93 \
  -o gen-out/zisk_tx_validate_against_block

REPO_ROOT="$(pwd)"

# run_case <name> <expected_status> <tx_chain> <block_chain>
#         <tx_gas> <block_gas> <tx_nonce> <account_nonce>
run_case() {
  local name="$1" expected_status="$2"
  local tx_chain="$3" block_chain="$4"
  local tx_gas="$5" block_gas="$6"
  local tx_nonce="$7" account_nonce="$8"

  local in_file="$REPO_ROOT/gen-out/zisk_tx_validate_against_block_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_tx_validate_against_block_${name}.output"

  python3 -c "
import struct, sys
out = struct.pack('<Q', $tx_chain)
out += struct.pack('<Q', $block_chain)
out += struct.pack('<Q', $tx_gas)
out += struct.pack('<Q', $block_gas)
out += struct.pack('<Q', $tx_nonce)
out += struct.pack('<Q', $account_nonce)
sys.stdout.buffer.write(out)
" > "$in_file"

  "$ZISKEMU" -e gen-out/zisk_tx_validate_against_block.elf \
    -i "$in_file" -o "$out_file" -n 500000 \
    >"$REPO_ROOT/gen-out/zisk_tx_validate_against_block_${name}.emu.log" 2>&1 || true

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
run_case "all_ok_mainnet"        0   1     1     21000     30000000 5  5  || FAILED=1
run_case "all_ok_genesis"        0   1     1     21000     30000000 0  0  || FAILED=1
run_case "all_ok_tight_gas"      0   1     1     30000000  30000000 1  1  || FAILED=1
run_case "all_ok_high_chain"     0   17000 17000 21000     30000000 5  5  || FAILED=1
# Chain mismatch (fail 1)
run_case "chain_mismatch"        1   2     1     21000     30000000 5  5  || FAILED=1
run_case "chain_mainnet_vs_test" 1   1     5     21000     30000000 5  5  || FAILED=1
# Gas over limit (fail 2)
run_case "gas_over_limit_small"  2   1     1     30000001  30000000 5  5  || FAILED=1
run_case "gas_over_limit_huge"   2   1     1     100000000 30000000 5  5  || FAILED=1
# Nonce mismatch (fail 3)
run_case "nonce_below"           3   1     1     21000     30000000 4  5  || FAILED=1
run_case "nonce_above"           3   1     1     21000     30000000 6  5  || FAILED=1
run_case "nonce_zero_vs_one"     3   1     1     21000     30000000 0  1  || FAILED=1
# Check ordering: chain → gas → nonce
run_case "chain_first_priority"  1   2     1     30000001  30000000 4  5  || FAILED=1  # all three fail; reports 1
run_case "gas_first_after_chain" 2   1     1     30000001  30000000 4  5  || FAILED=1  # gas + nonce fail; reports 2
# Edge: max u64 values
run_case "max_u64_match"         0   18446744073709551615 18446744073709551615 1 1 0 0 || FAILED=1
# Edge: 0 gas_limit, 0 tx_gas
run_case "zero_gas_ok"           0   1     1     0         0        0  0  || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: tx_validate_against_block enforces chain_id + gas_limit + nonce invariants"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
