#!/usr/bin/env bash
# codegen-zisk-validate-transaction-full-check.sh -- PR-K80.
#
# Top-level pre-EVM tx validator composing K76 + K79.
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

echo "==> emit zisk_validate_transaction_full ELF"
lake exe codegen --program zisk_validate_transaction_full --halt linux93 \
  -o gen-out/zisk_validate_transaction_full

REPO_ROOT="$(pwd)"

# run_case <name> <expected_status>
#         <tx_chain> <block_chain> <tx_gas> <block_gas>
#         <tx_nonce> <account_nonce> <is_creation> <data_hex>
#         <max_fee> <value> <balance>
run_case() {
  local name="$1" exp="$2"
  local tcv="$3" bcv="$4" tg="$5" bg="$6" tn="$7" an="$8"
  local ic="$9" dh="${10}"
  local mf="${11}" v="${12}" b="${13}"

  local in_file="$REPO_ROOT/gen-out/zisk_validate_transaction_full_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_validate_transaction_full_${name}.output"

  python3 -c "
import struct, sys
data = bytes.fromhex('$dh')
out  = struct.pack('<Q', $tcv)
out += struct.pack('<Q', $bcv)
out += struct.pack('<Q', $tg)
out += struct.pack('<Q', $bg)
out += struct.pack('<Q', $tn)
out += struct.pack('<Q', $an)
out += struct.pack('<Q', $ic)
out += struct.pack('<Q', len(data))
out += ($mf).to_bytes(32, 'big')
out += ($v).to_bytes(32, 'big')
out += ($b).to_bytes(32, 'big')
out += data
pad = (-len(out)) % 8
if pad:
    out += b'\x00' * pad
sys.stdout.buffer.write(out)
" > "$in_file"

  "$ZISKEMU" -e gen-out/zisk_validate_transaction_full.elf \
    -i "$in_file" -o "$out_file" -n 500000 \
    >"$REPO_ROOT/gen-out/zisk_validate_transaction_full_${name}.emu.log" 2>&1 || true

  local actual; actual="$(xxd -p -l 8 "$out_file" | tr -d '\n')"
  local exp_le; exp_le="$(python3 -c "print(int('$exp').to_bytes(8, 'little').hex())")"

  if [[ "$actual" == "$exp_le" ]]; then
    printf "  %-30s OK   status=%d\n" "$name" "$exp"
    return 0
  else
    printf "  %-30s FAIL  expected %d got 0x%s\n" "$name" "$exp" "$actual"
    return 1
  fi
}

GWEI=$(python3 -c "print(10**9)")
ETH=$(python3 -c "print(10**18)")
MF50=$(python3 -c "print(50 * 10**9)")
COST_50G_21K=$(python3 -c "print(50 * 10**9 * 21000)")
BAL_OK=$(python3 -c "print(10**18 + 50 * 10**9 * 21000)")  # 1 ETH value + gas

FAILED=0
# All pass
run_case "all_pass" \
  0 1 1 21000 30000000 5 5 0 "" "$MF50" "$ETH" "$BAL_OK"  || FAILED=1
# K76 step 1 fail (chain_id mismatch) → 101
run_case "k76_chain_fail" \
  101 5 1 21000 30000000 5 5 0 "" "$MF50" "$ETH" "$BAL_OK"  || FAILED=1
# K76 step 1 fail (gas overshoot block) → 102
run_case "k76_gas_block" \
  102 1 1 31000000 30000000 5 5 0 "" "$MF50" 0 "$BAL_OK"  || FAILED=1
# K76 step 1 fail (nonce mismatch) → 103
run_case "k76_nonce" \
  103 1 1 21000 30000000 5 6 0 "" "$MF50" "$ETH" "$BAL_OK"  || FAILED=1
# K76 step 2 fail (intrinsic > gas) → 201
run_case "k76_intrinsic" \
  201 1 1 20999 30000000 5 5 0 "" "$MF50" 0 "$BAL_OK"  || FAILED=1
# K79 step 1 fail (cost overflow) → 301
MAX256=115792089237316195423570985008687907853269984665640564039457584007913129639935
run_case "k79_cost_overflow" \
  301 1 1 21000 30000000 5 5 0 "" "$MAX256" 0 "$BAL_OK"  || FAILED=1
# K79 step 2 fail (insufficient balance) → 302
run_case "k79_insufficient" \
  302 1 1 21000 30000000 5 5 0 "" "$MF50" "$ETH" 0  || FAILED=1
# K76 priority over K79 (both would fail; K76 reported first)
run_case "k76_first_priority" \
  101 5 1 21000 30000000 5 5 0 "" "$MF50" "$ETH" 0  || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: validate_transaction_full routes through K76 + K79"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
