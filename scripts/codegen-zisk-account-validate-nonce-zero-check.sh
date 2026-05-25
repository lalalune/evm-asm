#!/usr/bin/env bash
# codegen-zisk-account-validate-nonce-zero-check.sh -- PR-K242.
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

echo "==> emit zisk_account_validate_nonce_zero ELF"
lake exe codegen --program zisk_account_validate_nonce_zero --halt linux93 \
  -o gen-out/zisk_account_validate_nonce_zero

REPO_ROOT="$(pwd)"

run_case() {
  local name="$1" nonce="$2" exp_zero="$3"

  local in_file="$REPO_ROOT/gen-out/zisk_account_validate_nonce_zero_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_account_validate_nonce_zero_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys, rlp
def u_be(n):
    if n == 0: return b''
    return n.to_bytes((n.bit_length() + 7) // 8, 'big')
n = $nonce
account = rlp.encode([
    u_be(n),               # nonce
    u_be(10**18),          # balance
    b'\\xaa'*32,           # storage_root
    b'\\xbb'*32,           # code_hash
])
with open(sys.argv[1], 'wb') as f:
    record = struct.pack('<Q', len(account)) + account
    f.write(record)
    pad = (-len(record)) % 8
    if pad: f.write(b'\x00' * pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_account_validate_nonce_zero.elf \
    -i "$in_file" -o "$out_file" -n 1000000 \
    >"$REPO_ROOT/gen-out/zisk_account_validate_nonce_zero_${name}.emu.log" 2>&1 || true

  local v_le; v_le="$(dd if="$out_file" bs=1 skip=8 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local actual; actual="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$v_le'))[0])")"

  if [[ "$actual" == "$exp_zero" ]]; then
    printf "  %-26s OK   is_zero=%s\n" "$name" "$actual"
    return 0
  else
    printf "  %-26s FAIL actual=%s expected=%s\n" "$name" "$actual" "$exp_zero"
    return 1
  fi
}

FAILED=0
run_case "zero_nonce"   0          1 || FAILED=1
run_case "one_nonce"    1          0 || FAILED=1
run_case "small_nonce"  42         0 || FAILED=1
run_case "big_nonce"    9999999999 0 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: account_validate_nonce_zero matches nonce == 0"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
