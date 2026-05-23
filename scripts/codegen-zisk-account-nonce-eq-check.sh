#!/usr/bin/env bash
# codegen-zisk-account-nonce-eq-check.sh -- PR-K136.
#
# Compare account.nonce against an expected u64.
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

echo "==> emit zisk_account_nonce_eq ELF"
lake exe codegen --program zisk_account_nonce_eq --halt linux93 \
  -o gen-out/zisk_account_nonce_eq

REPO_ROOT="$(pwd)"

# run_case <name> <account_nonce> <expected_nonce> <expected_is_equal>
run_case() {
  local name="$1" an="$2" en="$3" exp_eq="$4"

  local in_file="$REPO_ROOT/gen-out/zisk_account_nonce_eq_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_account_nonce_eq_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys, rlp
an = $an
en = $en
EMPTY_TRIE_ROOT = bytes.fromhex(
    '56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421')
EMPTY_CODE_HASH = bytes.fromhex(
    'c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470')
account = [an, 10**18, EMPTY_TRIE_ROOT, EMPTY_CODE_HASH]
account_rlp = rlp.encode(account)
with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(account_rlp)))
    f.write(struct.pack('<Q', en))
    f.write(account_rlp)
    pad = (-(16 + len(account_rlp))) % 8
    if pad: f.write(b'\x00' * pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_account_nonce_eq.elf \
    -i "$in_file" -o "$out_file" -n 1000000 \
    >"$REPO_ROOT/gen-out/zisk_account_nonce_eq_${name}.emu.log" 2>&1 || true

  local actual_status; actual_status="$(xxd -p -l 8 "$out_file" | tr -d '\n')"
  local actual_eq_le; actual_eq_le="$(dd if="$out_file" bs=1 skip=8 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local actual_eq; actual_eq="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$actual_eq_le'))[0])")"

  if [[ "$actual_status" == "0000000000000000" && "$actual_eq" == "$exp_eq" ]]; then
    printf "  %-28s OK   a=%d e=%d is_equal=%d\n" "$name" "$an" "$en" "$exp_eq"
    return 0
  else
    printf "  %-28s FAIL status=0x%s is_equal=%d expected=%d\n" "$name" "$actual_status" "$actual_eq" "$exp_eq"
    return 1
  fi
}

FAILED=0
run_case "match_zero"        0          0           1 || FAILED=1
run_case "match_one"         1          1           1 || FAILED=1
run_case "match_small"       42         42          1 || FAILED=1
run_case "match_large"       1099511627775 1099511627775 1 || FAILED=1
run_case "match_max_u64m1"   18446744073709551614 18446744073709551614 1 || FAILED=1
run_case "mismatch_diff"     5          6           0 || FAILED=1
run_case "mismatch_zero_v1"  0          1           0 || FAILED=1
run_case "mismatch_v1_zero"  1          0           0 || FAILED=1
run_case "mismatch_off_by_high" 256     1           0 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: account_nonce_eq compares account.nonce to expected"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
