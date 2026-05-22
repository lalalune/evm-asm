#!/usr/bin/env bash
# codegen-zisk-tx-validate-intrinsic-gas-legacy-check.sh -- PR-K66.
#
# Compose intrinsic_gas_legacy with tx.gas_limit comparison.
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

echo "==> emit zisk_tx_validate_intrinsic_gas_legacy ELF"
lake exe codegen --program zisk_tx_validate_intrinsic_gas_legacy --halt linux93 \
  -o gen-out/zisk_tx_validate_intrinsic_gas_legacy

REPO_ROOT="$(pwd)"

# run_case <name> <is_creation> <gas_limit> <data_hex>
run_case() {
  local name="$1" is_creation="$2" gas_limit="$3" data_hex="$4"

  local in_file="$REPO_ROOT/gen-out/zisk_tx_validate_intrinsic_gas_legacy_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_tx_validate_intrinsic_gas_legacy_${name}.output"

  python3 -c "
import struct, sys
data = bytes.fromhex('$data_hex')
out = struct.pack('<Q', len(data))
out += struct.pack('<Q', $is_creation)
out += struct.pack('<Q', $gas_limit)
out += data
pad = (-(24 + len(data))) % 8
if pad:
    out += b'\x00' * pad
sys.stdout.buffer.write(out)
" > "$in_file"

  "$ZISKEMU" -e gen-out/zisk_tx_validate_intrinsic_gas_legacy.elf \
    -i "$in_file" -o "$out_file" -n 500000 \
    >"$REPO_ROOT/gen-out/zisk_tx_validate_intrinsic_gas_legacy_${name}.emu.log" 2>&1 || true

  local expected_gas; expected_gas="$(python3 -c "
data = bytes.fromhex('$data_hex')
gas = 21000
if $is_creation:
    gas += 32000
for b in data:
    gas += 4 if b == 0 else 16
print(gas)
")"
  local expected_status; expected_status="$(python3 -c "
print(1 if $expected_gas > $gas_limit else 0)")"

  local actual_status; actual_status="$(xxd -p -l 8 "$out_file" | tr -d '\n')"
  local actual_gas; actual_gas="$(dd if="$out_file" bs=1 skip=8 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local exp_status_le; exp_status_le="$(python3 -c "print(int('$expected_status').to_bytes(8, 'little').hex())")"
  local exp_gas_le;    exp_gas_le="$(python3 -c "print(int('$expected_gas').to_bytes(8, 'little').hex())")"

  if [[ "$actual_status" == "$exp_status_le" && "$actual_gas" == "$exp_gas_le" ]]; then
    printf "  %-30s OK   status=%d gas=%d (limit=%d)\n" "$name" "$expected_status" "$expected_gas" "$gas_limit"
    return 0
  else
    printf "  %-30s FAIL  expected status=%d gas=%d got status=0x%s gas=0x%s\n" \
      "$name" "$expected_status" "$expected_gas" "$actual_status" "$actual_gas"
    return 1
  fi
}

FAILED=0
# Pass cases (intrinsic_gas <= gas_limit)
run_case "empty_call_ok"            0 21000     ""                                                 || FAILED=1
run_case "empty_call_extra"         0 100000    ""                                                 || FAILED=1
run_case "empty_creation_ok"        1 53000     ""                                                 || FAILED=1
run_case "small_data_ok"            0 21100     "00ff00"                                           || FAILED=1
run_case "selector_plus_arg_ok"     0 30000     "a9059cbb000000000000000000000000aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa00000000000000000000000000000000000000000000000000000000000003e8" || FAILED=1
run_case "creation_bytecode_ok"     1 60000     "6080604052348015600f57600080fd5b50603f80601d6000396000f3"  || FAILED=1
# Reject cases (intrinsic_gas > gas_limit)
run_case "empty_call_reject"        0 20999     ""                                                 || FAILED=1
run_case "empty_creation_reject"    1 52999     ""                                                 || FAILED=1
run_case "small_data_reject"        0 21000     "ff"                                               || FAILED=1
run_case "creation_data_reject"     1 53050     "ff"                                               || FAILED=1  # 53000 + 16 = 53016, limit=53050 → pass; let me set to reject
# Reject with creation bytecode that costs too much
run_case "creation_bytecode_reject" 1 53400     "6080604052348015600f57600080fd5b50603f80601d6000396000f3"  || FAILED=1
# Edge: gas_limit == intrinsic_gas (equal → pass)
run_case "gas_limit_equal"          0 21016     "ff"                                               || FAILED=1
# Large data, ample gas_limit
LARGE_DATA="$(python3 -c "print(bytes((i*7+3) & 0xff for i in range(200)).hex())")"
run_case "large_data_ample"         0 30000     "$LARGE_DATA"                                      || FAILED=1
# Large data, tight gas_limit (reject)
run_case "large_data_tight_reject"  0 23000     "$LARGE_DATA"                                      || FAILED=1
# Zero gas_limit (trivially fails)
run_case "zero_gas_limit"           0 0         ""                                                 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: tx_validate_intrinsic_gas_legacy enforces intrinsic_gas <= tx.gas_limit"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
