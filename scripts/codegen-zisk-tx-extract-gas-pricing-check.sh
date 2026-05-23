#!/usr/bin/env bash
# codegen-zisk-tx-extract-gas-pricing-check.sh -- PR-K108.
#
# Extract (max_priority_fee, max_fee) u256 BE pair from any tx type.
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

echo "==> emit zisk_tx_extract_gas_pricing ELF"
lake exe codegen --program zisk_tx_extract_gas_pricing --halt linux93 \
  -o gen-out/zisk_tx_extract_gas_pricing

REPO_ROOT="$(pwd)"

# run_case <name> <tx_type> <pri_fee> <max_fee_or_gas_price>
run_case() {
  local name="$1" t="$2" pri="$3" maxfee="$4"

  local in_file="$REPO_ROOT/gen-out/zisk_tx_extract_gas_pricing_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_tx_extract_gas_pricing_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys, rlp
tx_type = '$t'
pri = $pri
maxfee = $maxfee
ALICE = bytes([0xaa]*20)
R = int.from_bytes(bytes([0x11]*32), 'big')
S = int.from_bytes(bytes([0x22]*32), 'big')

if tx_type == 'legacy':
    # legacy: gas_price = maxfee; pri returned same as gas_price
    tx = [1, maxfee, 21000, ALICE, 10**18, b'', 27, R, S]
    tx_bytes = rlp.encode(tx)
    exp_pri = maxfee
    exp_max = maxfee
elif tx_type == 'eip2930':
    inner = [1, 7, maxfee, 21000, ALICE, 10**18, b'', [], 1, R, S]
    tx_bytes = b'\x01' + rlp.encode(inner)
    exp_pri = maxfee
    exp_max = maxfee
elif tx_type == 'eip1559':
    inner = [1, 7, pri, maxfee, 21000, ALICE, 10**18, b'', [], 1, R, S]
    tx_bytes = b'\x02' + rlp.encode(inner)
    exp_pri = pri
    exp_max = maxfee
elif tx_type == 'eip4844':
    H = bytes([0x01] + [0xab]*31)
    inner = [
        1, 7, pri, maxfee, 21000,
        ALICE, 10**18, b'', [],
        1, [H], 0, R, S,
    ]
    tx_bytes = b'\x03' + rlp.encode(inner)
    exp_pri = pri
    exp_max = maxfee
elif tx_type == 'eip7702':
    auth_list = [[1, ALICE, 0, 27, R, S]]
    inner = [1, 7, pri, maxfee, 21000, ALICE, 10**18, b'', [], auth_list, 1, R, S]
    tx_bytes = b'\x04' + rlp.encode(inner)
    exp_pri = pri
    exp_max = maxfee
else:
    raise ValueError(tx_type)

with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(tx_bytes)))
    f.write(tx_bytes)
    pad = (-(8 + len(tx_bytes))) % 8
    if pad: f.write(b'\x00' * pad)
with open(sys.argv[1] + '.exp_pri', 'wb') as f:
    f.write(exp_pri.to_bytes(32, 'big'))
with open(sys.argv[1] + '.exp_max', 'wb') as f:
    f.write(exp_max.to_bytes(32, 'big'))
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_tx_extract_gas_pricing.elf \
    -i "$in_file" -o "$out_file" -n 1000000 \
    >"$REPO_ROOT/gen-out/zisk_tx_extract_gas_pricing_${name}.emu.log" 2>&1 || true

  local actual_status; actual_status="$(xxd -p -l 8 "$out_file" | tr -d '\n')"
  local actual_pri; actual_pri="$(dd if="$out_file" bs=1 skip=8 count=32 2>/dev/null | xxd -p | tr -d '\n')"
  local actual_max; actual_max="$(dd if="$out_file" bs=1 skip=40 count=32 2>/dev/null | xxd -p | tr -d '\n')"
  local exp_pri; exp_pri="$(xxd -p "$in_file.exp_pri" | tr -d '\n')"
  local exp_max; exp_max="$(xxd -p "$in_file.exp_max" | tr -d '\n')"

  if [[ "$actual_status" == "0000000000000000" && "$actual_pri" == "$exp_pri" && "$actual_max" == "$exp_max" ]]; then
    printf "  %-32s OK   pri=%s.. max=%s..\n" "$name" "${actual_pri:0:10}" "${actual_max:0:10}"
    return 0
  else
    printf "  %-32s FAIL status=0x%s\n" "$name" "$actual_status"
    printf "    pri exp=%s\n    pri got=%s\n" "${exp_pri:0:16}" "${actual_pri:0:16}"
    printf "    max exp=%s\n    max got=%s\n" "${exp_max:0:16}" "${actual_max:0:16}"
    return 1
  fi
}

FAILED=0
run_case "legacy"          legacy   0         "10**9"      || FAILED=1
run_case "eip2930"         eip2930  0         "2*10**9"    || FAILED=1
run_case "eip1559_basic"   eip1559  "10**9"   "5*10**9"    || FAILED=1
run_case "eip1559_zero_pri" eip1559 0         "3*10**9"    || FAILED=1
run_case "eip4844"         eip4844  "2*10**9" "10*10**9"   || FAILED=1
run_case "eip7702"         eip7702  "3*10**9" "12*10**9"   || FAILED=1
run_case "eip1559_max_u128" eip1559 "(1<<127)" "(1<<128)-1" || FAILED=1
# Legacy with large gas_price (still u256)
run_case "legacy_big"      legacy   0         "(1<<200)"   || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: tx_extract_gas_pricing returns (max_priority_fee, max_fee) u256 BE"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
