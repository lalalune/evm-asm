#!/usr/bin/env bash
# codegen-zisk-account-extract-nonce-check.sh -- PR-K121.
#
# Extract u64 nonce (field 0) from account RLP.
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

echo "==> emit zisk_account_extract_nonce ELF"
lake exe codegen --program zisk_account_extract_nonce --halt linux93 \
  -o gen-out/zisk_account_extract_nonce

REPO_ROOT="$(pwd)"

# run_case <name> <nonce_python_expr>
run_case() {
  local name="$1" nonce_expr="$2"

  local in_file="$REPO_ROOT/gen-out/zisk_account_extract_nonce_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_account_extract_nonce_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys, rlp
nonce = $nonce_expr
account = [nonce, 10**18, bytes([0x11]*32), bytes([0x22]*32)]
account_rlp = rlp.encode(account)
with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(account_rlp)))
    f.write(account_rlp)
    pad = (-(8 + len(account_rlp))) % 8
    if pad: f.write(b'\x00' * pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_account_extract_nonce.elf \
    -i "$in_file" -o "$out_file" -n 1000000 \
    >"$REPO_ROOT/gen-out/zisk_account_extract_nonce_${name}.emu.log" 2>&1 || true

  local actual_status; actual_status="$(xxd -p -l 8 "$out_file" | tr -d '\n')"
  local actual_nonce_le; actual_nonce_le="$(dd if="$out_file" bs=1 skip=8 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local actual_nonce; actual_nonce="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$actual_nonce_le'))[0])")"
  local expected_nonce; expected_nonce="$(python3 -c "print($nonce_expr)")"

  if [[ "$actual_status" == "0000000000000000" && "$actual_nonce" == "$expected_nonce" ]]; then
    printf "  %-32s OK   nonce=%s\n" "$name" "$expected_nonce"
    return 0
  else
    printf "  %-32s FAIL status=0x%s nonce=%s expected=%s\n" "$name" "$actual_status" "$actual_nonce" "$expected_nonce"
    return 1
  fi
}

FAILED=0
run_case "zero"          "0"                          || FAILED=1
run_case "one"           "1"                          || FAILED=1
run_case "small"         "42"                         || FAILED=1
run_case "large"         "999999"                     || FAILED=1
run_case "u32_max"       "(1 << 32) - 1"              || FAILED=1
run_case "u48"           "1234567890123"              || FAILED=1
# EIP-2681: nonce capped at u64. RLP would truncate over-u64 anyway.
run_case "near_u64_max"  "(1 << 64) - 2"              || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: account_extract_nonce returns field 0 as u64"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
