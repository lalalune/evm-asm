#!/usr/bin/env bash
# codegen-zisk-tx-extract-value-check.sh -- PR-K103.
#
# Extract the `value` (u256 BE) field from any tx type.
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

echo "==> emit zisk_tx_extract_value ELF"
lake exe codegen --program zisk_tx_extract_value --halt linux93 \
  -o gen-out/zisk_tx_extract_value

REPO_ROOT="$(pwd)"

# run_case <name> <tx_type> <value> <expected_status>
# value is decimal (use 0x... for hex). Will be passed to Python.
run_case() {
  local name="$1" t="$2" value="$3" exp="$4"

  local in_file="$REPO_ROOT/gen-out/zisk_tx_extract_value_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_tx_extract_value_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys, rlp
tx_type = '$t'
value = $value
ALICE = bytes([0xaa]*20)
R = int.from_bytes(bytes([0x11]*32), 'big')
S = int.from_bytes(bytes([0x22]*32), 'big')

if tx_type == 'legacy':
    tx = [1, 10**9, 21000, ALICE, value, b'', 27, R, S]
    tx_bytes = rlp.encode(tx)
elif tx_type == 'eip2930':
    inner = [1, 7, 10**9, 21000, ALICE, value, b'', [], 1, R, S]
    tx_bytes = b'\x01' + rlp.encode(inner)
elif tx_type == 'eip1559':
    inner = [1, 7, 10**9, 2*10**9, 21000, ALICE, value, b'', [], 1, R, S]
    tx_bytes = b'\x02' + rlp.encode(inner)
elif tx_type == 'eip4844':
    H = bytes([0x01] + [0xab]*31)
    inner = [
        1, 7, 10**9, 2*10**9, 21000,
        ALICE, value, b'', [],
        1, [H], 0, R, S,
    ]
    tx_bytes = b'\x03' + rlp.encode(inner)
elif tx_type == 'eip7702':
    auth_list = [[1, ALICE, 0, 27, R, S]]
    inner = [1, 7, 10**9, 2*10**9, 21000, ALICE, value, b'', [], auth_list, 1, R, S]
    tx_bytes = b'\x04' + rlp.encode(inner)
else:
    raise ValueError(tx_type)

with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(tx_bytes)))
    f.write(tx_bytes)
    pad = (-(8 + len(tx_bytes))) % 8
    if pad: f.write(b'\x00' * pad)
with open(sys.argv[1] + '.expected', 'wb') as f:
    f.write(value.to_bytes(32, 'big'))
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_tx_extract_value.elf \
    -i "$in_file" -o "$out_file" -n 1000000 \
    >"$REPO_ROOT/gen-out/zisk_tx_extract_value_${name}.emu.log" 2>&1 || true

  local actual_status; actual_status="$(xxd -p -l 8 "$out_file" | tr -d '\n')"
  local actual_value; actual_value="$(dd if="$out_file" bs=1 skip=8 count=32 2>/dev/null | xxd -p | tr -d '\n')"
  local exp_status_le; exp_status_le="$(python3 -c "print(int('$exp').to_bytes(8, 'little').hex())")"
  local exp_value; exp_value="$(xxd -p "$in_file.expected" | tr -d '\n')"

  if [[ "$actual_status" == "$exp_status_le" && "$actual_value" == "$exp_value" ]]; then
    printf "  %-32s OK   value=%s..\n" "$name" "${actual_value:0:16}"
    return 0
  else
    printf "  %-32s FAIL status=0x%s value=0x%s\n" "$name" "$actual_status" "${actual_value:0:32}"
    return 1
  fi
}

FAILED=0
run_case "legacy_zero"        legacy    0                        0 || FAILED=1
run_case "legacy_1_eth"       legacy    "10**18"                 0 || FAILED=1
run_case "legacy_max_uint64"  legacy    "(1<<64)-1"              0 || FAILED=1
run_case "legacy_big_u128"    legacy    "(1<<128)-1"             0 || FAILED=1
run_case "legacy_big_u256"    legacy    "(1<<256)-1"             0 || FAILED=1
run_case "eip2930_1_eth"      eip2930   "10**18"                 0 || FAILED=1
run_case "eip1559_1_eth"      eip1559   "10**18"                 0 || FAILED=1
run_case "eip4844_1_eth"      eip4844   "10**18"                 0 || FAILED=1
run_case "eip7702_1_eth"      eip7702   "10**18"                 0 || FAILED=1
run_case "eip1559_big"        eip1559   "(1<<255)"               0 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: tx_extract_value returns value u256 BE across all tx types"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
