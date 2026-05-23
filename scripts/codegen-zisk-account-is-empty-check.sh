#!/usr/bin/env bash
# codegen-zisk-account-is-empty-check.sh -- PR-K123.
#
# EIP-161 empty-account predicate.
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

echo "==> emit zisk_account_is_empty ELF"
lake exe codegen --program zisk_account_is_empty --halt linux93 \
  -o gen-out/zisk_account_is_empty

REPO_ROOT="$(pwd)"

# run_case <name> <nonce> <balance> <code_hash_hex> <storage_root_hex> <expected_is_empty>
run_case() {
  local name="$1" nonce="$2" bal="$3" code_hash="$4" storage_root="$5" exp_empty="$6"

  local in_file="$REPO_ROOT/gen-out/zisk_account_is_empty_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_account_is_empty_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys, rlp
nonce = $nonce
bal = $bal
ch = bytes.fromhex('$code_hash')
sr = bytes.fromhex('$storage_root')
account = [nonce, bal, sr, ch]
account_rlp = rlp.encode(account)
with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(account_rlp)))
    f.write(account_rlp)
    pad = (-(8 + len(account_rlp))) % 8
    if pad: f.write(b'\x00' * pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_account_is_empty.elf \
    -i "$in_file" -o "$out_file" -n 1000000 \
    >"$REPO_ROOT/gen-out/zisk_account_is_empty_${name}.emu.log" 2>&1 || true

  local actual_status; actual_status="$(xxd -p -l 8 "$out_file" | tr -d '\n')"
  local actual_empty_le; actual_empty_le="$(dd if="$out_file" bs=1 skip=8 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local actual_empty; actual_empty="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$actual_empty_le'))[0])")"

  if [[ "$actual_status" == "0000000000000000" && "$actual_empty" == "$exp_empty" ]]; then
    printf "  %-32s OK   is_empty=%d\n" "$name" "$exp_empty"
    return 0
  else
    printf "  %-32s FAIL status=0x%s is_empty=%d expected=%d\n" "$name" "$actual_status" "$actual_empty" "$exp_empty"
    return 1
  fi
}

ECH="c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470"
ETR="56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421"
RCH="$(python3 -c "print('ab' * 32)")"
ZEROS="$(python3 -c "print('00' * 32)")"

FAILED=0
# Empty cases: nonce=0, balance=0, code_hash=EMPTY_CODE_HASH
run_case "empty_canonical"     0 0 "$ECH" "$ETR" 1 || FAILED=1
run_case "empty_zero_storage"  0 0 "$ECH" "$ZEROS" 1 || FAILED=1
# Non-empty cases
run_case "nonzero_nonce"       1 0 "$ECH" "$ETR" 0 || FAILED=1
run_case "nonzero_balance"     0 1 "$ECH" "$ETR" 0 || FAILED=1
run_case "contract_code"       0 0 "$RCH" "$ETR" 0 || FAILED=1
run_case "all_nonzero"         42 "10**18" "$RCH" "$ZEROS" 0 || FAILED=1
run_case "balance_big"         0 "(1 << 200)" "$ECH" "$ETR" 0 || FAILED=1
run_case "high_nonce_no_code"  99999 0 "$ECH" "$ETR" 0 || FAILED=1
# Empty with high storage_root — still empty per EIP-161
run_case "empty_high_storage"  0 0 "$ECH" "$(python3 -c "print('ff' * 32)")" 1 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: account_is_empty matches EIP-161 predicate"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
