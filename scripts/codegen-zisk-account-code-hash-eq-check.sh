#!/usr/bin/env bash
# codegen-zisk-account-code-hash-eq-check.sh -- PR-K135.
#
# Compare account.code_hash against an expected 32-byte hash.
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

echo "==> emit zisk_account_code_hash_eq ELF"
lake exe codegen --program zisk_account_code_hash_eq --halt linux93 \
  -o gen-out/zisk_account_code_hash_eq

REPO_ROOT="$(pwd)"

# run_case <name> <code_hash_hex> <expected_hex> <expected_is_equal>
run_case() {
  local name="$1" ch="$2" expected="$3" exp_eq="$4"

  local in_file="$REPO_ROOT/gen-out/zisk_account_code_hash_eq_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_account_code_hash_eq_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys, rlp
ch = bytes.fromhex('$ch')
expected = bytes.fromhex('$expected')
# Fix storage_root to EMPTY_TRIE_ROOT; vary code_hash field.
EMPTY_TRIE_ROOT = bytes.fromhex(
    '56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421')
account = [42, 10**18, EMPTY_TRIE_ROOT, ch]
account_rlp = rlp.encode(account)
with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(account_rlp)))
    f.write(expected)
    f.write(account_rlp)
    pad = (-(40 + len(account_rlp))) % 8
    if pad: f.write(b'\x00' * pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_account_code_hash_eq.elf \
    -i "$in_file" -o "$out_file" -n 1000000 \
    >"$REPO_ROOT/gen-out/zisk_account_code_hash_eq_${name}.emu.log" 2>&1 || true

  local actual_status; actual_status="$(xxd -p -l 8 "$out_file" | tr -d '\n')"
  local actual_eq_le; actual_eq_le="$(dd if="$out_file" bs=1 skip=8 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local actual_eq; actual_eq="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$actual_eq_le'))[0])")"

  if [[ "$actual_status" == "0000000000000000" && "$actual_eq" == "$exp_eq" ]]; then
    printf "  %-32s OK   is_equal=%d\n" "$name" "$exp_eq"
    return 0
  else
    printf "  %-32s FAIL status=0x%s is_equal=%d expected=%d\n" "$name" "$actual_status" "$actual_eq" "$exp_eq"
    return 1
  fi
}

R1="$(python3 -c "print('aa' * 32)")"
R2="$(python3 -c "print('bb' * 32)")"
ECH="c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470"
# One bit flipped at the end
R1_FLIP="$(python3 -c "print('aa' * 31 + 'ab')")"

FAILED=0
run_case "match"             "$R1"  "$R1"      1 || FAILED=1
run_case "match_ech"         "$ECH" "$ECH"     1 || FAILED=1
run_case "mismatch_diff"     "$R1"  "$R2"      0 || FAILED=1
run_case "mismatch_flip"     "$R1"  "$R1_FLIP" 0 || FAILED=1
run_case "match_zero"        "0000000000000000000000000000000000000000000000000000000000000000" "0000000000000000000000000000000000000000000000000000000000000000" 1 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: account_code_hash_eq compares account.code_hash to expected"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
