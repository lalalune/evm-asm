#!/usr/bin/env bash
# codegen-zisk-rlp-field-to-u256-be-check.sh -- PR-K35.
#
# Extract N-th RLP field as 32-byte BE u256.
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

echo "==> emit zisk_rlp_field_to_u256_be ELF"
lake exe codegen --program zisk_rlp_field_to_u256_be --halt linux93 \
  -o gen-out/zisk_rlp_field_to_u256_be

REPO_ROOT="$(pwd)"

run_case() {
  local name="$1" container_hex="$2" idx="$3" expected_status="$4" expected_value_hex="$5"

  local in_file="$REPO_ROOT/gen-out/zisk_rlp_field_to_u256_be_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_rlp_field_to_u256_be_${name}.output"

  python3 -c "
import struct, sys
container = bytes.fromhex('$container_hex')
with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(container)))
    f.write(struct.pack('<Q', $idx))
    f.write(container)
    pad = (-(16 + len(container))) % 8
    if pad:
        f.write(b'\x00' * pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_rlp_field_to_u256_be.elf \
    -i "$in_file" -o "$out_file" -n 50000 \
    >"$REPO_ROOT/gen-out/zisk_rlp_field_to_u256_be_${name}.emu.log" 2>&1 || true

  local actual_status actual_value exp_status_le
  actual_status="$(xxd -p -l 8 "$out_file" 2>/dev/null | tr -d '\n')"
  actual_value="$(dd if="$out_file" bs=1 skip=8 count=32 2>/dev/null | xxd -p | tr -d '\n')"
  exp_status_le="$(python3 -c "print(int('$expected_status').to_bytes(8, 'little').hex())")"

  if [[ "$actual_status" == "$exp_status_le" && "$actual_value" == "$expected_value_hex" ]]; then
    printf "  %-26s OK   status=%d value=%s...\n" "$name" "$expected_status" "${expected_value_hex:0:32}"
    return 0
  else
    printf "  %-26s FAIL\n    expected: status=%d value=%s\n    actual:   status=0x%s value=%s\n" \
      "$name" "$expected_status" "$expected_value_hex" "$actual_status" "$actual_value"
    return 1
  fi
}

RLP_ENCODE_LIST() {
  uv run --directory execution-specs --quiet python3 -c "
import rlp, sys
items = []
for arg in sys.argv[1:]:
    if arg == 'EMPTY':
        items.append(b'')
    elif arg.startswith('INT:'):
        items.append(int(arg[4:]))
    elif arg.startswith('HEX:'):
        items.append(bytes.fromhex(arg[4:]))
    else:
        items.append(arg.encode())
print(rlp.encode(items).hex())
" "$@"
}

LEGACY_TX="$(RLP_ENCODE_LIST INT:7 INT:1000000000 INT:21000 HEX:$(printf 'aa%.0s' $(seq 1 20)) INT:1000000000000000000 EMPTY INT:27 HEX:$(printf '11%.0s' $(seq 1 32)) HEX:$(printf '22%.0s' $(seq 1 32)))"
LARGE_U256_LIST="$(RLP_ENCODE_LIST INT:0 INT:115792089237316195423570985008687907853269984665640564039457584007913129639935)"
ZERO_PAD_32="0000000000000000000000000000000000000000000000000000000000000000"

# Expected helper: pad-to-32 BE.
pad_be32() {
  python3 -c "
import sys
val = int(sys.argv[1])
print(val.to_bytes(32, 'big').hex())
" "$1"
}

FAILED=0
# tx[0] = nonce = 7 → BE 32-byte (left-zero-padded)
run_case "tx_nonce"          "$LEGACY_TX" 0 0 "$(pad_be32 7)"                                 || FAILED=1
# tx[1] = gas_price = 10^9
run_case "tx_gas_price"      "$LEGACY_TX" 1 0 "$(pad_be32 1000000000)"                       || FAILED=1
# tx[4] = value = 10^18
run_case "tx_value"          "$LEGACY_TX" 4 0 "$(pad_be32 1000000000000000000)"              || FAILED=1
# tx[7] = r = 32 bytes 0x11 → already 32 bytes
run_case "tx_r"              "$LEGACY_TX" 7 0 "$(printf '11%.0s' $(seq 1 32))"               || FAILED=1
# tx[8] = s = 32 bytes 0x22
run_case "tx_s"              "$LEGACY_TX" 8 0 "$(printf '22%.0s' $(seq 1 32))"               || FAILED=1
# tx[3] = to = 20 bytes (≤ 32, valid u256)
run_case "tx_to_as_u256"     "$LEGACY_TX" 3 0 "$(printf '00%.0s' $(seq 1 12))$(printf 'aa%.0s' $(seq 1 20))" || FAILED=1
# tx[5] = data = empty → all zeros
run_case "tx_empty_data"     "$LEGACY_TX" 5 0 "$ZERO_PAD_32"                                 || FAILED=1
# OOB
run_case "tx_oob"            "$LEGACY_TX" 9 1 "$ZERO_PAD_32"                                 || FAILED=1
# Max u256 (full 32 bytes)
run_case "max_u256"          "$LARGE_U256_LIST" 1 0 "$(printf 'ff%.0s' $(seq 1 32))"         || FAILED=1
# Zero in u256 form
run_case "zero_u256"         "$LARGE_U256_LIST" 0 0 "$ZERO_PAD_32"                           || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: rlp_field_to_u256_be decodes every u256-sized field shape"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
