#!/usr/bin/env bash
# codegen-zisk-account-validate-code-hash-empty-check.sh -- PR-K234.
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

echo "==> emit zisk_account_validate_code_hash_empty ELF"
lake exe codegen --program zisk_account_validate_code_hash_empty --halt linux93 \
  -o gen-out/zisk_account_validate_code_hash_empty

REPO_ROOT="$(pwd)"

EMPTY_HASH_HEX="c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470"

run_case() {
  local name="$1" code_hash_hex="$2" exp_empty="$3"

  local in_file="$REPO_ROOT/gen-out/zisk_account_validate_code_hash_empty_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_account_validate_code_hash_empty_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys, rlp
def u_be(n):
    if n == 0: return b''
    return n.to_bytes((n.bit_length() + 7) // 8, 'big')

code_hash = bytes.fromhex('$code_hash_hex')
account = rlp.encode([
    u_be(7),               # nonce
    u_be(10**18),          # balance (1 ETH)
    b'\\xaa'*32,           # storage_root (irrelevant)
    code_hash,
])
with open(sys.argv[1], 'wb') as f:
    record = struct.pack('<Q', len(account)) + account
    f.write(record)
    pad = (-len(record)) % 8
    if pad: f.write(b'\x00' * pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_account_validate_code_hash_empty.elf \
    -i "$in_file" -o "$out_file" -n 1000000 \
    >"$REPO_ROOT/gen-out/zisk_account_validate_code_hash_empty_${name}.emu.log" 2>&1 || true

  local v_le; v_le="$(dd if="$out_file" bs=1 skip=8 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local actual; actual="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$v_le'))[0])")"

  if [[ "$actual" == "$exp_empty" ]]; then
    printf "  %-26s OK   is_empty=%s\n" "$name" "$actual"
    return 0
  else
    printf "  %-26s FAIL actual=%s expected=%s\n" "$name" "$actual" "$exp_empty"
    return 1
  fi
}

FAILED=0
run_case "eoa_empty"     "$EMPTY_HASH_HEX"                                                  1 || FAILED=1
run_case "contract_a"    "0000000000000000000000000000000000000000000000000000000000000001" 0 || FAILED=1
run_case "contract_b"    "1234567890abcdef1234567890abcdef1234567890abcdef1234567890abcdef" 0 || FAILED=1
run_case "all_ff"        "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff" 0 || FAILED=1
run_case "near_empty"    "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a471" 0 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: account_validate_code_hash_empty matches code_hash == EMPTY_CODE_HASH"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
