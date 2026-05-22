#!/usr/bin/env bash
# codegen-zisk-calldata-byte-counts-check.sh -- PR-K105.
#
# Count zero/non-zero bytes for intrinsic-gas pricing.
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

echo "==> emit zisk_calldata_byte_counts ELF"
lake exe codegen --program zisk_calldata_byte_counts --halt linux93 \
  -o gen-out/zisk_calldata_byte_counts

REPO_ROOT="$(pwd)"

# run_case <name> <bytes_hex>
run_case() {
  local name="$1" bytes_hex="$2"

  local in_file="$REPO_ROOT/gen-out/zisk_calldata_byte_counts_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_calldata_byte_counts_${name}.output"

  python3 -c "
import struct, sys
b = bytes.fromhex('$bytes_hex')
with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(b)))
    f.write(b)
    pad = (-(8 + len(b))) % 8
    if pad: f.write(b'\x00' * pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_calldata_byte_counts.elf \
    -i "$in_file" -o "$out_file" -n 5000000 \
    >"$REPO_ROOT/gen-out/zisk_calldata_byte_counts_${name}.emu.log" 2>&1 || true

  local actual_status; actual_status="$(xxd -p -l 8 "$out_file" | tr -d '\n')"
  local actual_zero_le; actual_zero_le="$(dd if="$out_file" bs=1 skip=8 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local actual_nz_le; actual_nz_le="$(dd if="$out_file" bs=1 skip=16 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local actual_zero; actual_zero="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$actual_zero_le'))[0])")"
  local actual_nz; actual_nz="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$actual_nz_le'))[0])")"
  local exp_zero; exp_zero="$(python3 -c "b = bytes.fromhex('$bytes_hex'); print(b.count(0))")"
  local exp_nz; exp_nz="$(python3 -c "b = bytes.fromhex('$bytes_hex'); print(len(b) - b.count(0))")"

  if [[ "$actual_status" == "0000000000000000" && "$actual_zero" == "$exp_zero" && "$actual_nz" == "$exp_nz" ]]; then
    printf "  %-32s OK   zeros=%d non_zeros=%d\n" "$name" "$exp_zero" "$exp_nz"
    return 0
  else
    printf "  %-32s FAIL status=0x%s zeros=%d nz=%d expected zeros=%d nz=%d\n" "$name" "$actual_status" "$actual_zero" "$actual_nz" "$exp_zero" "$exp_nz"
    return 1
  fi
}

FAILED=0
run_case "empty"               ""                                              || FAILED=1
run_case "all_zeros_4"         "00000000"                                      || FAILED=1
run_case "all_nz_4"            "deadbeef"                                      || FAILED=1
run_case "mixed_4"             "00ff00ff"                                      || FAILED=1
run_case "single_zero"         "00"                                            || FAILED=1
run_case "single_nz"           "ff"                                            || FAILED=1
run_case "selector"            "a9059cbb"                                      || FAILED=1
run_case "erc20_transfer" \
  "a9059cbb000000000000000000000000aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0000000000000000000000000000000000000000000000000de0b6b3a7640000" \
  || FAILED=1
# Large buffer
run_case "alternating_256"    "$(python3 -c "print('00ff' * 128)")"            || FAILED=1
run_case "all_zeros_512"      "$(python3 -c "print('00' * 512)")"              || FAILED=1
run_case "all_nz_512"         "$(python3 -c "print('ab' * 512)")"              || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: calldata_byte_counts returns (zero_count, non_zero_count)"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
