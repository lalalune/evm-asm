#!/usr/bin/env bash
# codegen-zisk-account-extract-balance-check.sh -- PR-K120.
#
# Extract balance (u256 BE) from account RLP.
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

echo "==> emit zisk_account_extract_balance ELF"
lake exe codegen --program zisk_account_extract_balance --halt linux93 \
  -o gen-out/zisk_account_extract_balance

REPO_ROOT="$(pwd)"

# run_case <name> <balance_python_expr>
run_case() {
  local name="$1" bal_expr="$2"

  local in_file="$REPO_ROOT/gen-out/zisk_account_extract_balance_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_account_extract_balance_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys, rlp
bal = $bal_expr
account = [42, bal, bytes([0x11]*32), bytes([0x22]*32)]
account_rlp = rlp.encode(account)
with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(account_rlp)))
    f.write(account_rlp)
    pad = (-(8 + len(account_rlp))) % 8
    if pad: f.write(b'\x00' * pad)
with open(sys.argv[1] + '.expected', 'wb') as f:
    f.write(bal.to_bytes(32, 'big'))
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_account_extract_balance.elf \
    -i "$in_file" -o "$out_file" -n 1000000 \
    >"$REPO_ROOT/gen-out/zisk_account_extract_balance_${name}.emu.log" 2>&1 || true

  local actual_status; actual_status="$(xxd -p -l 8 "$out_file" | tr -d '\n')"
  local actual_bal; actual_bal="$(dd if="$out_file" bs=1 skip=8 count=32 2>/dev/null | xxd -p | tr -d '\n')"
  local expected_bal; expected_bal="$(xxd -p "$in_file.expected" | tr -d '\n')"

  if [[ "$actual_status" == "0000000000000000" && "$actual_bal" == "$expected_bal" ]]; then
    printf "  %-32s OK   bal=%s..\n" "$name" "${actual_bal:0:16}"
    return 0
  else
    printf "  %-32s FAIL status=0x%s bal=%s expected=%s\n" "$name" "$actual_status" "${actual_bal:0:16}" "${expected_bal:0:16}"
    return 1
  fi
}

FAILED=0
run_case "zero"               "0"                          || FAILED=1
run_case "one_wei"            "1"                          || FAILED=1
run_case "one_eth"            "10**18"                     || FAILED=1
run_case "ten_eth"            "10 * 10**18"                || FAILED=1
run_case "u64_max"            "(1 << 64) - 1"              || FAILED=1
run_case "u128_max"           "(1 << 128) - 1"             || FAILED=1
run_case "u200"               "(1 << 200) - 1"             || FAILED=1
run_case "high_bit"           "1 << 255"                   || FAILED=1
run_case "u256_max"           "(1 << 256) - 1"             || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: account_extract_balance returns field 1 as u256 BE"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
