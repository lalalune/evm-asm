#!/usr/bin/env bash
# codegen-zisk-withdrawal-decode-check.sh -- PR-K49.
#
# Decode a Withdrawal RLP record (post-Shanghai):
#   rlp([index, validator_index, address, amount])
# into a 48-byte flat struct.
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

echo "==> emit zisk_withdrawal_decode ELF"
lake exe codegen --program zisk_withdrawal_decode --halt linux93 \
  -o gen-out/zisk_withdrawal_decode

REPO_ROOT="$(pwd)"

# run_case <name> <index> <validator_index> <address_hex> <amount_gwei>
run_case() {
  local name="$1" index="$2" validator_idx="$3" addr_hex="$4" amount="$5"

  local in_file="$REPO_ROOT/gen-out/zisk_withdrawal_decode_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_withdrawal_decode_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_withdrawal_decode_${name}.expected"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys
import rlp

index = $index
validator_idx = $validator_idx
addr = bytes.fromhex('$addr_hex')
amount = $amount

wd_rlp = rlp.encode([index, validator_idx, addr, amount])
with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(wd_rlp)))
    f.write(wd_rlp)
    pad = (-(8 + len(wd_rlp))) % 8
    if pad:
        f.write(b'\x00' * pad)

# Expected: status u64 LE + 48-byte struct.
expected = struct.pack('<Q', 0)
expected += struct.pack('<Q', index)
expected += struct.pack('<Q', validator_idx)
expected += addr.ljust(20, b'\x00')
expected += b'\x00' * 4  # pad
expected += struct.pack('<Q', amount)
with open(sys.argv[2], 'wb') as f:
    f.write(expected)
" "$in_file" "$exp_file"

  "$ZISKEMU" -e gen-out/zisk_withdrawal_decode.elf \
    -i "$in_file" -o "$out_file" -n 500000 \
    >"$REPO_ROOT/gen-out/zisk_withdrawal_decode_${name}.emu.log" 2>&1 || true

  local exp_size; exp_size="$(stat -c%s "$exp_file")"
  local actual expected
  actual="$(xxd -p -l "$exp_size" "$out_file" 2>/dev/null | tr -d '\n')"
  expected="$(xxd -p -l "$exp_size" "$exp_file" 2>/dev/null | tr -d '\n')"

  if [[ "$actual" == "$expected" ]]; then
    printf "  %-30s OK   index=%d validator=%d amount_gwei=%d\n" \
      "$name" "$index" "$validator_idx" "$amount"
    return 0
  else
    printf "  %-30s FAIL\n    expected: %s\n    actual:   %s\n" \
      "$name" "$expected" "$actual"
    return 1
  fi
}

ALICE="aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
BOB="bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"

FAILED=0
# Standard withdrawal (typical mainnet shape)
run_case "typical"     1000 12345 "$ALICE" 1000000000           || FAILED=1
# Zero index, zero validator, zero amount (degenerate but spec-allowed)
run_case "zero_all"    0    0     "$ALICE" 0                    || FAILED=1
# Genesis-style: index 0, validator_index 0
run_case "first_wd"    0    1     "$BOB"   32000000000          || FAILED=1
# Big index (≈ 2^32 — past 4B mainnet withdrawals)
run_case "big_index"   5000000000 999 "$ALICE" 1000             || FAILED=1
# Max u64 amount (5.8e19 wei equivalent)
run_case "max_amount"  100 200 "$BOB" 18446744073709551615      || FAILED=1
# Validator with huge index (some PoS testnets reach 2^31)
run_case "big_validator" 7 4294967295 "$ALICE" 28000000000      || FAILED=1
# A Capella-genesis-like sequence
run_case "epoch_start" 99000 100000 "$ALICE" 31000000000        || FAILED=1
# Withdrawal amount typical (partial = excess over 32 ETH stake)
run_case "partial_wd"  88 1234 "$BOB" 1500000000                || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: withdrawal_decode produces the spec-compliant 4-field struct"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
