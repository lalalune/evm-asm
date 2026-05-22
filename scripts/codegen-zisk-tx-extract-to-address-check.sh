#!/usr/bin/env bash
# codegen-zisk-tx-extract-to-address-check.sh -- PR-K101.
#
# Extract `to` address + is_creation flag from any tx type.
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

echo "==> emit zisk_tx_extract_to_address ELF"
lake exe codegen --program zisk_tx_extract_to_address --halt linux93 \
  -o gen-out/zisk_tx_extract_to_address

REPO_ROOT="$(pwd)"

# run_case <name> <tx_type> <to_hex> <expected_status> <expected_is_creation>
run_case() {
  local name="$1" t="$2" to="$3" exp_status="$4" exp_creation="$5"

  local in_file="$REPO_ROOT/gen-out/zisk_tx_extract_to_address_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_tx_extract_to_address_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys, rlp
tx_type = '$t'
to_bytes = bytes.fromhex('$to')
R = int.from_bytes(bytes([0x11]*32), 'big')
S = int.from_bytes(bytes([0x22]*32), 'big')

if tx_type == 'legacy':
    tx = [1, 10**9, 21000, to_bytes, 10**18, b'', 27, R, S]
    tx_bytes = rlp.encode(tx)
elif tx_type == 'eip2930':
    inner = [1, 7, 10**9, 21000, to_bytes, 10**18, b'', [], 1, R, S]
    tx_bytes = b'\x01' + rlp.encode(inner)
elif tx_type == 'eip1559':
    inner = [1, 7, 10**9, 2*10**9, 21000, to_bytes, 10**18, b'', [], 1, R, S]
    tx_bytes = b'\x02' + rlp.encode(inner)
elif tx_type == 'eip4844':
    H = bytes([0x01] + [0xab]*31)
    inner = [
        1, 7, 10**9, 2*10**9, 21000,
        to_bytes, 10**18, b'', [],
        1, [H], 0, R, S,
    ]
    tx_bytes = b'\x03' + rlp.encode(inner)
elif tx_type == 'eip7702':
    auth_list = [[1, bytes([0xcc]*20), 0, 27, R, S]]
    inner = [1, 7, 10**9, 2*10**9, 21000, to_bytes, 10**18, b'', [], auth_list, 1, R, S]
    tx_bytes = b'\x04' + rlp.encode(inner)
elif tx_type == 'invalid':
    tx_bytes = b'\x7f\x00'
else:
    raise ValueError(tx_type)

with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(tx_bytes)))
    f.write(tx_bytes)
    pad = (-(8 + len(tx_bytes))) % 8
    if pad: f.write(b'\x00' * pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_tx_extract_to_address.elf \
    -i "$in_file" -o "$out_file" -n 1000000 \
    >"$REPO_ROOT/gen-out/zisk_tx_extract_to_address_${name}.emu.log" 2>&1 || true

  local actual_status; actual_status="$(xxd -p -l 8 "$out_file" | tr -d '\n')"
  local actual_addr; actual_addr="$(dd if="$out_file" bs=1 skip=8 count=20 2>/dev/null | xxd -p | tr -d '\n')"
  local actual_creation; actual_creation="$(dd if="$out_file" bs=1 skip=32 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local exp_status_le; exp_status_le="$(python3 -c "print(int('$exp_status').to_bytes(8, 'little').hex())")"
  local exp_creation_le; exp_creation_le="$(python3 -c "print(int('$exp_creation').to_bytes(8, 'little').hex())")"

  if [[ "$actual_status" != "$exp_status_le" ]]; then
    printf "  %-32s FAIL status=0x%s expected=%d\n" "$name" "$actual_status" "$exp_status"
    return 1
  fi
  if [[ "$actual_creation" != "$exp_creation_le" ]]; then
    printf "  %-32s FAIL is_creation=0x%s expected=%d\n" "$name" "$actual_creation" "$exp_creation"
    return 1
  fi
  if [[ "$exp_status" == "0" && "$exp_creation" == "0" ]]; then
    if [[ "$actual_addr" != "$to" ]]; then
      printf "  %-32s FAIL addr=0x%s expected=0x%s\n" "$name" "$actual_addr" "$to"
      return 1
    fi
  fi
  if [[ "$exp_status" == "0" && "$exp_creation" == "0" ]]; then
    printf "  %-32s OK   to=0x%s\n" "$name" "${actual_addr:0:8}.."
  elif [[ "$exp_status" == "0" ]]; then
    printf "  %-32s OK   is_creation\n" "$name"
  else
    printf "  %-32s OK   status=%d (rejected)\n" "$name" "$exp_status"
  fi
  return 0
}

ALICE="aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
BOB="bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"
EMPTY=""

FAILED=0
run_case "legacy_to"          legacy   "$ALICE" 0 0 || FAILED=1
run_case "legacy_create"      legacy   "$EMPTY" 0 1 || FAILED=1
run_case "eip2930_to"         eip2930  "$ALICE" 0 0 || FAILED=1
run_case "eip2930_create"     eip2930  "$EMPTY" 0 1 || FAILED=1
run_case "eip1559_to"         eip1559  "$BOB"   0 0 || FAILED=1
run_case "eip1559_create"     eip1559  "$EMPTY" 0 1 || FAILED=1
run_case "eip4844_to"         eip4844  "$ALICE" 0 0 || FAILED=1
run_case "eip7702_to"         eip7702  "$BOB"   0 0 || FAILED=1
run_case "invalid_type"       invalid  "$EMPTY" 1 0 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: tx_extract_to_address returns to+is_creation across all tx types"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
