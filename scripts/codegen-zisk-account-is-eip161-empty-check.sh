#!/usr/bin/env bash
# codegen-zisk-account-is-eip161-empty-check.sh -- PR-K137.
#
# EIP-161 empty-account predicate:
#   nonce == 0 AND balance == 0 AND code_hash == EMPTY_CODE_HASH.
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

echo "==> emit zisk_account_is_eip161_empty ELF"
lake exe codegen --program zisk_account_is_eip161_empty --halt linux93 \
  -o gen-out/zisk_account_is_eip161_empty

REPO_ROOT="$(pwd)"

# run_case <name> <nonce> <balance> <code_hash_hex> <expected_is_empty>
run_case() {
  local name="$1" nonce="$2" balance="$3" ch="$4" exp="$5"

  local in_file="$REPO_ROOT/gen-out/zisk_account_is_eip161_empty_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_account_is_eip161_empty_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys, rlp
EMPTY_TRIE_ROOT = bytes.fromhex(
    '56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421')
nonce = $nonce
balance = $balance
ch = bytes.fromhex('$ch')
account = [nonce, balance, EMPTY_TRIE_ROOT, ch]
account_rlp = rlp.encode(account)
with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(account_rlp)))
    f.write(account_rlp)
    pad = (-(8 + len(account_rlp))) % 8
    if pad: f.write(b'\x00' * pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_account_is_eip161_empty.elf \
    -i "$in_file" -o "$out_file" -n 1000000 \
    >"$REPO_ROOT/gen-out/zisk_account_is_eip161_empty_${name}.emu.log" 2>&1 || true

  local actual_status; actual_status="$(xxd -p -l 8 "$out_file" | tr -d '\n')"
  local actual_eq_le; actual_eq_le="$(dd if="$out_file" bs=1 skip=8 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local actual_eq; actual_eq="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$actual_eq_le'))[0])")"

  if [[ "$actual_status" == "0000000000000000" && "$actual_eq" == "$exp" ]]; then
    printf "  %-30s OK   nonce=%d bal=%d is_empty=%d\n" "$name" "$nonce" "$balance" "$exp"
    return 0
  else
    printf "  %-30s FAIL status=0x%s is_empty=%d expected=%d\n" "$name" "$actual_status" "$actual_eq" "$exp"
    return 1
  fi
}

ECH="c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470"
OCH="aa$(python3 -c "print('00' * 31)")"

FAILED=0
# Positive cases: should be empty
run_case "empty_minimal"   0 0          "$ECH" 1 || FAILED=1

# Negative cases: any one field non-empty
run_case "neg_nonce"       1 0          "$ECH" 0 || FAILED=1
run_case "neg_big_nonce"   1000000 0    "$ECH" 0 || FAILED=1
run_case "neg_balance"     0 1          "$ECH" 0 || FAILED=1
run_case "neg_big_balance" 0 1000000000000000000 "$ECH" 0 || FAILED=1
run_case "neg_max_balance" 0 $((2**63 - 1)) "$ECH" 0 || FAILED=1
run_case "neg_codehash"    0 0          "$OCH"   0 || FAILED=1
run_case "neg_all_fields"  42 999       "$OCH"   0 || FAILED=1

# Zero-byte boundary: balance = 0 has b'' in RLP (length 0); confirm canonical path.
# Non-canonical encodings (length>0, value 0) shouldn't occur in real state but the
# byte-loop is robust anyway.

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: account_is_eip161_empty matches EIP-161 spec"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
