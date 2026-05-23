#!/usr/bin/env bash
# codegen-zisk-tx-eip1559-extract-signature-check.sh -- PR-K139.
#
# Extract (y_parity, r, s) from the inner RLP of an EIP-1559 tx.
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

echo "==> emit zisk_tx_eip1559_extract_signature ELF"
lake exe codegen --program zisk_tx_eip1559_extract_signature --halt linux93 \
  -o gen-out/zisk_tx_eip1559_extract_signature

REPO_ROOT="$(pwd)"

# run_case <name> <y_parity> <r_hex> <s_hex>
run_case() {
  local name="$1" y="$2" r="$3" s="$4"

  local in_file="$REPO_ROOT/gen-out/zisk_tx_eip1559_extract_signature_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_tx_eip1559_extract_signature_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys, rlp
y = $y
r = int.from_bytes(bytes.fromhex('$r'), 'big')
s = int.from_bytes(bytes.fromhex('$s'), 'big')
ALICE = bytes([0xaa] * 20)
inner = [1, 42, 10**9, 2*10**9, 21000, ALICE, 10**18, b'', [], y, r, s]
inner_rlp = rlp.encode(inner)
with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(inner_rlp)))
    f.write(inner_rlp)
    pad = (-(8 + len(inner_rlp))) % 8
    if pad: f.write(b'\x00' * pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_tx_eip1559_extract_signature.elf \
    -i "$in_file" -o "$out_file" -n 1000000 \
    >"$REPO_ROOT/gen-out/zisk_tx_eip1559_extract_signature_${name}.emu.log" 2>&1 || true

  local actual_status; actual_status="$(xxd -p -l 8 "$out_file" | tr -d '\n')"
  local actual_y_le;   actual_y_le="$(dd if="$out_file" bs=1 skip=8  count=8  2>/dev/null | xxd -p | tr -d '\n')"
  local actual_r;      actual_r="$(dd if="$out_file" bs=1 skip=16 count=32 2>/dev/null | xxd -p | tr -d '\n')"
  local actual_s;      actual_s="$(dd if="$out_file" bs=1 skip=48 count=32 2>/dev/null | xxd -p | tr -d '\n')"
  local actual_y;      actual_y="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$actual_y_le'))[0])")"

  local exp_r; exp_r="$(python3 -c "v=bytes.fromhex('$r'); print(('00'*(32-len(v)) + '$r'))")"
  local exp_s; exp_s="$(python3 -c "v=bytes.fromhex('$s'); print(('00'*(32-len(v)) + '$s'))")"

  if [[ "$actual_status" == "0000000000000000" \
       && "$actual_y" == "$y" \
       && "$actual_r" == "$exp_r" \
       && "$actual_s" == "$exp_s" ]]; then
    printf "  %-30s OK   y=%d r=%s... s=%s...\n" "$name" "$y" "${actual_r:0:8}" "${actual_s:0:8}"
    return 0
  else
    printf "  %-30s FAIL status=0x%s y=%d expected=%d\n" "$name" "$actual_status" "$actual_y" "$y"
    printf "      r got %s\n      r exp %s\n" "$actual_r" "$exp_r"
    printf "      s got %s\n      s exp %s\n" "$actual_s" "$exp_s"
    return 1
  fi
}

R32="1111111111111111111111111111111111111111111111111111111111111111"
S32="2222222222222222222222222222222222222222222222222222222222222222"
R_SHORT="cafebabe"
S_SHORT="deadbeef00"

FAILED=0
# y_parity == 0
run_case "y0_full"                0  "$R32"      "$S32"     || FAILED=1
# y_parity == 1
run_case "y1_full"                1  "$R32"      "$S32"     || FAILED=1
# Short r, s (canonical RLP)
run_case "y0_short_rs"            0  "$R_SHORT"  "$S_SHORT" || FAILED=1
# Smallest non-zero
run_case "y1_min_rs"              1  "01"        "01"       || FAILED=1
# Boundary: r leading-zero word
run_case "y0_r_leading_zero_word" 0  "0000000000000001${R32:16}" "$S32" || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: tx_eip1559_extract_signature recovers (y_parity, r, s) correctly"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
