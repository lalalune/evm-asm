#!/usr/bin/env bash
# codegen-zisk-account-extract-code-hash-check.sh -- PR-K122.
#
# Extract code_hash (32 B field 3) from account RLP.
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

echo "==> emit zisk_account_extract_code_hash ELF"
lake exe codegen --program zisk_account_extract_code_hash --halt linux93 \
  -o gen-out/zisk_account_extract_code_hash

REPO_ROOT="$(pwd)"

# run_case <name> <code_hash_hex> <expected_status>
run_case() {
  local name="$1" code_hash="$2" exp_status="${3:-0}"

  local in_file="$REPO_ROOT/gen-out/zisk_account_extract_code_hash_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_account_extract_code_hash_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys, rlp
code_hash = bytes.fromhex('$code_hash') if '$code_hash' else b''
if len(code_hash) == 0:
    # 3-field account (missing code_hash) — should fail
    account = [0, 10**18, bytes([0x11]*32)]
else:
    account = [0, 10**18, bytes([0x11]*32), code_hash]
account_rlp = rlp.encode(account)
with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(account_rlp)))
    f.write(account_rlp)
    pad = (-(8 + len(account_rlp))) % 8
    if pad: f.write(b'\x00' * pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_account_extract_code_hash.elf \
    -i "$in_file" -o "$out_file" -n 1000000 \
    >"$REPO_ROOT/gen-out/zisk_account_extract_code_hash_${name}.emu.log" 2>&1 || true

  local actual_status; actual_status="$(xxd -p -l 8 "$out_file" | tr -d '\n')"
  local exp_status_le; exp_status_le="$(python3 -c "print(int('$exp_status').to_bytes(8, 'little').hex())")"

  if [[ "$actual_status" != "$exp_status_le" ]]; then
    printf "  %-32s FAIL status=0x%s expected=%d\n" "$name" "$actual_status" "$exp_status"
    return 1
  fi
  if [[ "$exp_status" != "0" ]]; then
    printf "  %-32s OK   status=%d (rejected)\n" "$name" "$exp_status"
    return 0
  fi
  local actual_hash; actual_hash="$(dd if="$out_file" bs=1 skip=8 count=32 2>/dev/null | xxd -p | tr -d '\n')"
  if [[ "$actual_hash" == "$code_hash" ]]; then
    printf "  %-32s OK   hash=%s..\n" "$name" "${actual_hash:0:16}"
    return 0
  else
    printf "  %-32s FAIL\n    expected: %s\n    actual:   %s\n" "$name" "$code_hash" "$actual_hash"
    return 1
  fi
}

FAILED=0
EMPTY_CODE_HASH="c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470"
RANDOM_HASH="$(python3 -c "print('ab' * 32)")"
ANOTHER_HASH="$(python3 -c "print('de' * 32)")"

run_case "empty_code_hash_eoa" "$EMPTY_CODE_HASH"  || FAILED=1
run_case "contract_random"     "$RANDOM_HASH"     || FAILED=1
run_case "contract_de"         "$ANOTHER_HASH"    || FAILED=1
run_case "missing_field3"      ""                  1 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: account_extract_code_hash returns field 3"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
