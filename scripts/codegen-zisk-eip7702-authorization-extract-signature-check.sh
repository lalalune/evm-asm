#!/usr/bin/env bash
# codegen-zisk-eip7702-authorization-extract-signature-check.sh -- PR-K143.
#
# Extract (y_parity, r, s) from a single EIP-7702 authorization
# tuple: rlp([chain_id, address, nonce, y_parity, r, s]).
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

echo "==> emit zisk_eip7702_authorization_extract_signature ELF"
lake exe codegen --program zisk_eip7702_authorization_extract_signature --halt linux93 \
  -o gen-out/zisk_eip7702_authorization_extract_signature

REPO_ROOT="$(pwd)"

# run_case <name> <chain_id> <nonce> <y_parity> <r_hex> <s_hex>
run_case() {
  local name="$1" cid="$2" nonce="$3" y="$4" r="$5" s="$6"

  local in_file="$REPO_ROOT/gen-out/zisk_eip7702_authorization_extract_signature_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_eip7702_authorization_extract_signature_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys, rlp
cid = $cid
nonce = $nonce
y = $y
r = int.from_bytes(bytes.fromhex('$r'), 'big')
s = int.from_bytes(bytes.fromhex('$s'), 'big')
DELEGATE = bytes([0xde] * 20)
tuple_rlp = rlp.encode([cid, DELEGATE, nonce, y, r, s])
with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(tuple_rlp)))
    f.write(tuple_rlp)
    pad = (-(8 + len(tuple_rlp))) % 8
    if pad: f.write(b'\x00' * pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_eip7702_authorization_extract_signature.elf \
    -i "$in_file" -o "$out_file" -n 1000000 \
    >"$REPO_ROOT/gen-out/zisk_eip7702_authorization_extract_signature_${name}.emu.log" 2>&1 || true

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
    printf "  %-30s OK   cid=%d nonce=%d y=%d r=%s... s=%s...\n" "$name" "$cid" "$nonce" "$y" "${actual_r:0:8}" "${actual_s:0:8}"
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
# Mainnet chain_id, typical nonces, y_parity ∈ {0, 1}
run_case "mainnet_y0"             1   42       0  "$R32"      "$S32"     || FAILED=1
run_case "mainnet_y1"             1   42       1  "$R32"      "$S32"     || FAILED=1
# Sepolia-like big chain_id (>8 bytes? no, fits in 4)
run_case "sepolia_y0"             11155111 99  0  "$R32"      "$S32"     || FAILED=1
# nonce=0 boundary (RLP-canonical empty bytes)
run_case "nonce_zero"             1   0        1  "$R32"      "$S32"     || FAILED=1
# Short r/s
run_case "short_rs"               1   1        0  "$R_SHORT"  "$S_SHORT" || FAILED=1
# Smallest non-zero r/s
run_case "min_rs"                 1   1        1  "01"        "01"       || FAILED=1
# r leading-zero word
run_case "r_leading_zero"         1   1        0  "0000000000000001${R32:16}" "$S32" || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: eip7702_authorization_extract_signature recovers (y_parity, r, s) correctly"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
