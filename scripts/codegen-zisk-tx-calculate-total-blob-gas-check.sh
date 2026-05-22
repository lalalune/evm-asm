#!/usr/bin/env bash
# codegen-zisk-tx-calculate-total-blob-gas-check.sh -- PR-K92.
#
# Per-tx blob gas: 0 for non-type-3, count*gas_per_blob for type-3.
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

echo "==> emit zisk_tx_calculate_total_blob_gas ELF"
lake exe codegen --program zisk_tx_calculate_total_blob_gas --halt linux93 \
  -o gen-out/zisk_tx_calculate_total_blob_gas

REPO_ROOT="$(pwd)"

# run_case <name> <type> <blobs> <gas_per_blob> <expected_status> <expected_gas>
# type: "legacy"|"eip1559"|"eip2930"|"eip4844"|"eip7702"|"invalid"
run_case() {
  local name="$1" tx_type="$2" blobs="$3" gpb="$4" exp_status="$5" exp_gas="$6"

  local in_file="$REPO_ROOT/gen-out/zisk_tx_calculate_total_blob_gas_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_tx_calculate_total_blob_gas_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys, rlp
tx_type = '$tx_type'
n = $blobs
gpb = $gpb
ALICE = bytes([0xaa]*20)
R = int.from_bytes(bytes([0x11]*32), 'big')
S = int.from_bytes(bytes([0x22]*32), 'big')

if tx_type == 'legacy':
    tx = [1, 10**9, 21000, ALICE, 10**18, b'', 27, R, S]
    tx_bytes = rlp.encode(tx)
elif tx_type == 'eip1559':
    inner = [1, 7, 10**9, 2*10**9, 21000, ALICE, 10**18, b'', [], 1, R, S]
    tx_bytes = b'\x02' + rlp.encode(inner)
elif tx_type == 'eip2930':
    inner = [1, 7, 10**9, 21000, ALICE, 10**18, b'', [], 1, R, S]
    tx_bytes = b'\x01' + rlp.encode(inner)
elif tx_type == 'eip4844':
    H = bytes([0x01] + [0xab]*31)
    inner = [
        1, 7, 10**9, 2*10**9, 21000,
        ALICE, 10**18, b'', [],
        1, [H]*n, 0,
        R, S,
    ]
    tx_bytes = b'\x03' + rlp.encode(inner)
elif tx_type == 'eip7702':
    auth_list = [[1, ALICE, 0, 27, R, S]]
    inner = [1, 7, 10**9, 2*10**9, 21000, ALICE, 10**18, b'', [], auth_list, 1, R, S]
    tx_bytes = b'\x04' + rlp.encode(inner)
elif tx_type == 'invalid':
    tx_bytes = b'\x7f\x00\x00'  # 0x7f is unassigned tx type
else:
    raise ValueError(tx_type)

with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(tx_bytes)))
    f.write(struct.pack('<Q', gpb))
    f.write(tx_bytes)
    pad = (-(16 + len(tx_bytes))) % 8
    if pad: f.write(b'\x00' * pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_tx_calculate_total_blob_gas.elf \
    -i "$in_file" -o "$out_file" -n 1000000 \
    >"$REPO_ROOT/gen-out/zisk_tx_calculate_total_blob_gas_${name}.emu.log" 2>&1 || true

  local actual_status; actual_status="$(xxd -p -l 8 "$out_file" | tr -d '\n')"
  local actual_gas; actual_gas="$(dd if="$out_file" bs=1 skip=8 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local exp_status_le; exp_status_le="$(python3 -c "print(int('$exp_status').to_bytes(8, 'little').hex())")"
  local exp_gas_le; exp_gas_le="$(python3 -c "print(int('$exp_gas').to_bytes(8, 'little').hex())")"

  if [[ "$actual_status" == "$exp_status_le" && "$actual_gas" == "$exp_gas_le" ]]; then
    printf "  %-32s OK   status=%d gas=%s\n" "$name" "$exp_status" "$exp_gas"
    return 0
  else
    printf "  %-32s FAIL status=0x%s gas=0x%s (expected status=%d gas=%s)\n" "$name" "$actual_status" "$actual_gas" "$exp_status" "$exp_gas"
    return 1
  fi
}

GPB=131072

FAILED=0
run_case "legacy"            legacy   0 "$GPB" 0 0                || FAILED=1
run_case "eip1559"           eip1559  0 "$GPB" 0 0                || FAILED=1
run_case "eip2930"           eip2930  0 "$GPB" 0 0                || FAILED=1
run_case "eip7702"           eip7702  0 "$GPB" 0 0                || FAILED=1
run_case "eip4844_one"       eip4844  1 "$GPB" 0 131072           || FAILED=1
run_case "eip4844_three"     eip4844  3 "$GPB" 0 393216           || FAILED=1
run_case "eip4844_six"       eip4844  6 "$GPB" 0 786432           || FAILED=1
run_case "eip4844_custom_gpb" eip4844 2 1000   0 2000             || FAILED=1
run_case "invalid_type"      invalid  0 "$GPB" 1 0                || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: tx_calculate_total_blob_gas returns count*gas_per_blob for type-3, 0 otherwise"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
