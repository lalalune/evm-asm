#!/usr/bin/env bash
# codegen-zisk-account-has-empty-code-check.sh -- PR-K131.
#
# Predicate: code_hash == EMPTY_CODE_HASH?
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

echo "==> emit zisk_account_has_empty_code ELF"
lake exe codegen --program zisk_account_has_empty_code --halt linux93 \
  -o gen-out/zisk_account_has_empty_code

REPO_ROOT="$(pwd)"

# run_case <name> <nonce> <balance_expr> <code_hash_hex> <expected_is_eoa>
run_case() {
  local name="$1" nonce="$2" bal="$3" code_hash="$4" exp_eoa="$5"

  local in_file="$REPO_ROOT/gen-out/zisk_account_has_empty_code_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_account_has_empty_code_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys, rlp
nonce = $nonce
bal = $bal
ch = bytes.fromhex('$code_hash')
account = [nonce, bal, bytes([0x11]*32), ch]
account_rlp = rlp.encode(account)
with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(account_rlp)))
    f.write(account_rlp)
    pad = (-(8 + len(account_rlp))) % 8
    if pad: f.write(b'\x00' * pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_account_has_empty_code.elf \
    -i "$in_file" -o "$out_file" -n 1000000 \
    >"$REPO_ROOT/gen-out/zisk_account_has_empty_code_${name}.emu.log" 2>&1 || true

  local actual_status; actual_status="$(xxd -p -l 8 "$out_file" | tr -d '\n')"
  local actual_eoa_le; actual_eoa_le="$(dd if="$out_file" bs=1 skip=8 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local actual_eoa; actual_eoa="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$actual_eoa_le'))[0])")"

  if [[ "$actual_status" == "0000000000000000" && "$actual_eoa" == "$exp_eoa" ]]; then
    printf "  %-32s OK   is_eoa=%d\n" "$name" "$exp_eoa"
    return 0
  else
    printf "  %-32s FAIL status=0x%s is_eoa=%d expected=%d\n" "$name" "$actual_status" "$actual_eoa" "$exp_eoa"
    return 1
  fi
}

ECH="c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470"
RCH="$(python3 -c "print('ab' * 32)")"

FAILED=0
# EOA cases (code_hash == EMPTY_CODE_HASH)
run_case "eoa_zero_nonce"      0     0          "$ECH" 1 || FAILED=1
run_case "eoa_with_balance"    0     "10**18"   "$ECH" 1 || FAILED=1
run_case "eoa_with_nonce"      42    "10**18"   "$ECH" 1 || FAILED=1
# Contract cases (code_hash != EMPTY_CODE_HASH)
run_case "contract_zero"       0     0          "$RCH" 0 || FAILED=1
run_case "contract_normal"     1     "10**18"   "$RCH" 0 || FAILED=1
run_case "contract_dead_zero"  0     0          "$(python3 -c "print('00' * 32)")" 0 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: account_has_empty_code matches code_hash == EMPTY_CODE_HASH"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
