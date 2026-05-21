#!/usr/bin/env bash
# codegen-zisk-rlp-field-to-u64-check.sh -- PR-K34.
#
# Extract the N-th field of an RLP list and decode as a u64.
# Used by future tx-decode / header-decode for nonce-shaped
# fields.
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

echo "==> emit zisk_rlp_field_to_u64 ELF"
lake exe codegen --program zisk_rlp_field_to_u64 --halt linux93 \
  -o gen-out/zisk_rlp_field_to_u64

REPO_ROOT="$(pwd)"

run_case() {
  local name="$1" container_hex="$2" idx="$3" expected_status="$4" expected_value="$5"

  local in_file="$REPO_ROOT/gen-out/zisk_rlp_field_to_u64_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_rlp_field_to_u64_${name}.output"

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

  "$ZISKEMU" -e gen-out/zisk_rlp_field_to_u64.elf \
    -i "$in_file" -o "$out_file" -n 50000 \
    >"$REPO_ROOT/gen-out/zisk_rlp_field_to_u64_${name}.emu.log" 2>&1 || true

  local actual_status actual_value
  actual_status="$(xxd -p -l 8 "$out_file" 2>/dev/null | tr -d '\n')"
  actual_value="$(dd if="$out_file" bs=1 skip=8 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local exp_status_le exp_value_le
  exp_status_le="$(python3 -c "print(int('$expected_status').to_bytes(8, 'little').hex())")"
  exp_value_le="$(python3 -c "print(int('$expected_value').to_bytes(8, 'little').hex())")"

  if [[ "$actual_status" == "$exp_status_le" && "$actual_value" == "$exp_value_le" ]]; then
    printf "  %-26s OK   status=%d value=%d\n" "$name" "$expected_status" "$expected_value"
    return 0
  else
    printf "  %-26s FAIL\n    expected: status=%d value=%d\n    actual:   status=0x%s value=0x%s\n" \
      "$name" "$expected_status" "$expected_value" "$actual_status" "$actual_value"
    return 1
  fi
}

# RLP encode helpers in Python.
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

# Build a legacy-tx-shaped 9-field list with known values for testing.
LEGACY_TX="$(RLP_ENCODE_LIST INT:7 INT:1000000000 INT:21000 HEX:$(printf 'aa%.0s' $(seq 1 20)) INT:1000000000000000000 EMPTY INT:27 HEX:$(printf '11%.0s' $(seq 1 32)) HEX:$(printf '22%.0s' $(seq 1 32)))"

# Simple test list: [0, 1, 127, 128, 256, 65535, 4294967296, 18446744073709551615]
SIMPLE_LIST="$(RLP_ENCODE_LIST INT:0 INT:1 INT:127 INT:128 INT:256 INT:65535 INT:4294967296 INT:18446744073709551615)"

# Mixed: [u64_42, "hello", u64_99]
MIXED_LIST="$(RLP_ENCODE_LIST INT:42 hello INT:99)"

FAILED=0
# tx[0] = nonce = 7
run_case "tx_nonce"        "$LEGACY_TX" 0 0 7                                          || FAILED=1
# tx[1] = gas_price = 10^9 — too long for u64? 10^9 = 0x3B9ACA00 (4 bytes). Fits.
run_case "tx_gas_price"    "$LEGACY_TX" 1 0 1000000000                                 || FAILED=1
# tx[2] = gas_limit = 21000
run_case "tx_gas_limit"    "$LEGACY_TX" 2 0 21000                                      || FAILED=1
# tx[4] = value = 10^18 = 0x0DE0B6B3A7640000 (8 bytes). Fits u64 exactly.
run_case "tx_value_u64"    "$LEGACY_TX" 4 0 1000000000000000000                        || FAILED=1
# tx[6] = v = 27
run_case "tx_v"            "$LEGACY_TX" 6 0 27                                         || FAILED=1
# tx[7] = r = 32 bytes — too long, status=2.
run_case "tx_r_too_long"   "$LEGACY_TX" 7 2 0                                          || FAILED=1
# tx[3] = to = 20 bytes — too long, status=2.
run_case "tx_to_too_long"  "$LEGACY_TX" 3 2 0                                          || FAILED=1
# Out of bounds.
run_case "tx_oob"          "$LEGACY_TX" 9 1 0                                          || FAILED=1
# Simple list values.
run_case "simple_zero"     "$SIMPLE_LIST" 0 0 0                                        || FAILED=1
run_case "simple_one"      "$SIMPLE_LIST" 1 0 1                                        || FAILED=1
run_case "simple_127"      "$SIMPLE_LIST" 2 0 127                                      || FAILED=1
run_case "simple_128"      "$SIMPLE_LIST" 3 0 128                                      || FAILED=1
run_case "simple_max_u64"  "$SIMPLE_LIST" 7 0 18446744073709551615                     || FAILED=1
# Mixed: field 1 = "hello" (5-byte string). Decoded as u64 (5 bytes BE).
HELLO_U64="$(python3 -c "print(int.from_bytes(b'hello', 'big'))")"
run_case "mixed_string"    "$MIXED_LIST" 1 0 "$HELLO_U64"                              || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: rlp_field_to_u64 decodes every u64-sized field shape"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
