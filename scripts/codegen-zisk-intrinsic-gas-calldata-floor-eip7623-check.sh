#!/usr/bin/env bash
# codegen-zisk-intrinsic-gas-calldata-floor-eip7623-check.sh -- PR-K106.
#
# EIP-7623 calldata-floor gas cost.
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

echo "==> emit zisk_intrinsic_gas_calldata_floor_eip7623 ELF"
lake exe codegen --program zisk_intrinsic_gas_calldata_floor_eip7623 --halt linux93 \
  -o gen-out/zisk_intrinsic_gas_calldata_floor_eip7623

REPO_ROOT="$(pwd)"

GAS_TX_BASE=21000
GAS_FLOOR_PER_TOKEN=10
TOKEN_PER_NONZERO=4

# run_case <name> <data_hex>
run_case() {
  local name="$1" data_hex="$2"

  local in_file="$REPO_ROOT/gen-out/zisk_intrinsic_gas_calldata_floor_eip7623_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_intrinsic_gas_calldata_floor_eip7623_${name}.output"

  python3 -c "
import struct, sys
d = bytes.fromhex('$data_hex')
with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(d)))
    f.write(struct.pack('<Q', $GAS_FLOOR_PER_TOKEN))
    f.write(struct.pack('<Q', $TOKEN_PER_NONZERO))
    f.write(struct.pack('<Q', $GAS_TX_BASE))
    f.write(d)
    pad = (-(32 + len(d))) % 8
    if pad: f.write(b'\x00' * pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_intrinsic_gas_calldata_floor_eip7623.elf \
    -i "$in_file" -o "$out_file" -n 5000000 \
    >"$REPO_ROOT/gen-out/zisk_intrinsic_gas_calldata_floor_eip7623_${name}.emu.log" 2>&1 || true

  local actual_status; actual_status="$(xxd -p -l 8 "$out_file" | tr -d '\n')"
  local actual_floor_le; actual_floor_le="$(dd if="$out_file" bs=1 skip=8 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local actual_floor; actual_floor="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$actual_floor_le'))[0])")"
  local expected_floor; expected_floor="$(python3 -c "
d = bytes.fromhex('$data_hex')
z = d.count(0)
nz = len(d) - z
tokens = z + nz * $TOKEN_PER_NONZERO
floor = tokens * $GAS_FLOOR_PER_TOKEN + $GAS_TX_BASE
print(floor)
")"

  if [[ "$actual_status" == "0000000000000000" && "$actual_floor" == "$expected_floor" ]]; then
    printf "  %-32s OK   floor=%d\n" "$name" "$expected_floor"
    return 0
  else
    printf "  %-32s FAIL floor=%d expected=%d\n" "$name" "$actual_floor" "$expected_floor"
    return 1
  fi
}

FAILED=0
run_case "empty"             "" || FAILED=1
run_case "all_zeros_4"       "00000000" || FAILED=1
run_case "all_nz_4"          "deadbeef" || FAILED=1
run_case "mixed_4"           "00ff00ff" || FAILED=1
run_case "selector"          "a9059cbb" || FAILED=1
run_case "erc20_transfer" \
  "a9059cbb000000000000000000000000aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0000000000000000000000000000000000000000000000000de0b6b3a7640000" \
  || FAILED=1
run_case "alternating_256"   "$(python3 -c "print('00ff' * 128)")" || FAILED=1
run_case "all_zeros_1024"    "$(python3 -c "print('00' * 1024)")"  || FAILED=1
run_case "all_nz_1024"       "$(python3 -c "print('ab' * 1024)")"  || FAILED=1
# Init-code sized buffers
run_case "init_code"         "6080604052348015600f57600080fd5b50603f80601d6000396000f3fe" || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: intrinsic_gas_calldata_floor_eip7623 matches tokens*10 + 21000"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
