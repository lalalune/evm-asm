#!/usr/bin/env bash
# codegen-zisk-withdrawal-rlp-encode-check.sh -- PR-K130.
#
# RLP-encode an EIP-4895 Withdrawal.
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

echo "==> emit zisk_withdrawal_rlp_encode ELF"
lake exe codegen --program zisk_withdrawal_rlp_encode --halt linux93 \
  -o gen-out/zisk_withdrawal_rlp_encode

REPO_ROOT="$(pwd)"

# run_case <name> <index> <validator> <address_hex> <amount>
run_case() {
  local name="$1" idx="$2" val="$3" addr="$4" amt="$5"

  local in_file="$REPO_ROOT/gen-out/zisk_withdrawal_rlp_encode_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_withdrawal_rlp_encode_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys, rlp
idx = $idx
val = $val
amt = $amt
addr = bytes.fromhex('$addr')
expected = rlp.encode([idx, val, addr, amt])
with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', idx))
    f.write(struct.pack('<Q', val))
    f.write(struct.pack('<Q', amt))
    f.write(b'\x00' * 8)  # padding to 32B before address
    f.write(addr)
    pad = (-(40 + 20)) % 8
    if pad: f.write(b'\x00' * pad)
with open(sys.argv[1] + '.expected', 'wb') as f:
    f.write(struct.pack('<Q', len(expected)))
    f.write(expected)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_withdrawal_rlp_encode.elf \
    -i "$in_file" -o "$out_file" -n 1000000 \
    >"$REPO_ROOT/gen-out/zisk_withdrawal_rlp_encode_${name}.emu.log" 2>&1 || true

  local actual_status; actual_status="$(xxd -p -l 8 "$out_file" | tr -d '\n')"
  local actual_len_le; actual_len_le="$(dd if="$out_file" bs=1 skip=8 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local actual_len; actual_len="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$actual_len_le'))[0])")"
  local expected_len_le; expected_len_le="$(dd if="$in_file.expected" bs=1 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local expected_len; expected_len="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$expected_len_le'))[0])")"

  if [[ "$actual_status" != "0000000000000000" ]]; then
    printf "  %-32s FAIL status=0x%s\n" "$name" "$actual_status"
    return 1
  fi
  if [[ "$actual_len" != "$expected_len" ]]; then
    printf "  %-32s FAIL len=%d expected=%d\n" "$name" "$actual_len" "$expected_len"
    return 1
  fi
  local actual_bytes; actual_bytes="$(dd if="$out_file" bs=1 skip=16 count="$actual_len" 2>/dev/null | xxd -p | tr -d '\n')"
  local expected_bytes; expected_bytes="$(dd if="$in_file.expected" bs=1 skip=8 count="$expected_len" 2>/dev/null | xxd -p | tr -d '\n')"
  if [[ "$actual_bytes" == "$expected_bytes" ]]; then
    printf "  %-32s OK   len=%d\n" "$name" "$actual_len"
    return 0
  else
    printf "  %-32s FAIL\n    expected: %s\n    actual:   %s\n" "$name" "$expected_bytes" "$actual_bytes"
    return 1
  fi
}

ALICE="aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
BOB="bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"
ZERO="0000000000000000000000000000000000000000"

FAILED=0
run_case "all_zero"           0     0     "$ZERO"  0                       || FAILED=1
run_case "simple"             1     1     "$ALICE" "10**9"                 || FAILED=1
run_case "small_values"       42    100   "$ALICE" "$((32 * 10**9))"       || FAILED=1
run_case "large_index"        65536 1000  "$BOB"   "$((1000 * 10**9))"     || FAILED=1
run_case "huge_index"         "(1<<48)" "(1<<32)" "$ALICE" "$((10**15))"   || FAILED=1
run_case "max_u64_index"      "(1<<64)-1" "(1<<64)-1" "$BOB" "(1<<64)-1"   || FAILED=1
run_case "small_amount"       7     8     "$ALICE" 1                       || FAILED=1
run_case "amount_127"         5     5     "$BOB"   127                     || FAILED=1
run_case "amount_128"         5     5     "$BOB"   128                     || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: withdrawal_rlp_encode matches Python rlp.encode([idx, val, addr, amt])"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
