#!/usr/bin/env bash
# codegen-zisk-tx-legacy-extract-signature-check.sh -- PR-K138.
#
# Extract (v, r, s) from a 9-field legacy transaction RLP.
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

echo "==> emit zisk_tx_legacy_extract_signature ELF"
lake exe codegen --program zisk_tx_legacy_extract_signature --halt linux93 \
  -o gen-out/zisk_tx_legacy_extract_signature

REPO_ROOT="$(pwd)"

# run_case <name> <v> <r_hex> <s_hex>
run_case() {
  local name="$1" v="$2" r="$3" s="$4"

  local in_file="$REPO_ROOT/gen-out/zisk_tx_legacy_extract_signature_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_tx_legacy_extract_signature_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys, rlp
v = $v
r = int.from_bytes(bytes.fromhex('$r'), 'big')
s = int.from_bytes(bytes.fromhex('$s'), 'big')
ALICE = bytes([0xaa] * 20)
tx = [42, 10**9, 21000, ALICE, 10**18, b'', v, r, s]
tx_rlp = rlp.encode(tx)
with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(tx_rlp)))
    f.write(tx_rlp)
    pad = (-(8 + len(tx_rlp))) % 8
    if pad: f.write(b'\x00' * pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_tx_legacy_extract_signature.elf \
    -i "$in_file" -o "$out_file" -n 1000000 \
    >"$REPO_ROOT/gen-out/zisk_tx_legacy_extract_signature_${name}.emu.log" 2>&1 || true

  local actual_status; actual_status="$(xxd -p -l 8 "$out_file" | tr -d '\n')"
  local actual_v_le;   actual_v_le="$(dd if="$out_file" bs=1 skip=8  count=8  2>/dev/null | xxd -p | tr -d '\n')"
  local actual_r;      actual_r="$(dd if="$out_file" bs=1 skip=16 count=32 2>/dev/null | xxd -p | tr -d '\n')"
  local actual_s;      actual_s="$(dd if="$out_file" bs=1 skip=48 count=32 2>/dev/null | xxd -p | tr -d '\n')"
  local actual_v;      actual_v="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$actual_v_le'))[0])")"

  # Expected r/s right-aligned, zero-padded to 32 bytes.
  local exp_r; exp_r="$(python3 -c "import sys; v=bytes.fromhex('$r'); print(('00'*(32-len(v)) + '$r'))")"
  local exp_s; exp_s="$(python3 -c "import sys; v=bytes.fromhex('$s'); print(('00'*(32-len(v)) + '$s'))")"

  if [[ "$actual_status" == "0000000000000000" \
       && "$actual_v" == "$v" \
       && "$actual_r" == "$exp_r" \
       && "$actual_s" == "$exp_s" ]]; then
    printf "  %-30s OK   v=%d r=%s... s=%s...\n" "$name" "$v" "${actual_r:0:8}" "${actual_s:0:8}"
    return 0
  else
    printf "  %-30s FAIL status=0x%s v=%d expected=%d\n" "$name" "$actual_status" "$actual_v" "$v"
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
# v == 27 pre-EIP-155 with full 32-byte r, s
run_case "preeip155_v27"     27   "$R32" "$S32"  || FAILED=1
# v == 28 pre-EIP-155
run_case "preeip155_v28"     28   "$R32" "$S32"  || FAILED=1
# EIP-155 mainnet v == 37 (chain_id=1)
run_case "eip155_v37"        37   "$R32" "$S32"  || FAILED=1
# Big v: chain_id=11155111 (Sepolia-like) → v = 22310240 or 22310241
run_case "eip155_big_v"      22310241 "$R32" "$S32"  || FAILED=1
# Short r, s (canonical RLP omits leading zeros)
run_case "short_r_short_s"   28  "$R_SHORT" "$S_SHORT"  || FAILED=1
# r leading-zero word case
run_case "r_with_leading_zeros" 27 "01" "01"  || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: tx_legacy_extract_signature recovers (v, r, s) correctly"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
