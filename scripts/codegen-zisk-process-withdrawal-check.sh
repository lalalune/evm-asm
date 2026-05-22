#!/usr/bin/env bash
# codegen-zisk-process-withdrawal-check.sh -- PR-K77.
#
# Credit account.balance += withdrawal.amount × 10^9.
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

echo "==> emit zisk_process_withdrawal ELF"
lake exe codegen --program zisk_process_withdrawal --halt linux93 \
  -o gen-out/zisk_process_withdrawal

REPO_ROOT="$(pwd)"

# run_case <name> <wd_index> <wd_validator> <wd_addr_hex> <wd_amount_gwei> <initial_balance_wei>
run_case() {
  local name="$1" wi="$2" wv="$3" wa="$4" amt="$5" bal="$6"

  local in_file="$REPO_ROOT/gen-out/zisk_process_withdrawal_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_process_withdrawal_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_process_withdrawal_${name}.expected"

  python3 -c "
import struct, sys
wi, wv, amt, bal = $wi, $wv, $amt, $bal
wa = bytes.fromhex('$wa')
# Build withdrawal struct (48 B):
#   0..8 index, 8..16 validator, 16..36 addr (20B), 36..40 pad, 40..48 amount
struct_bytes  = struct.pack('<Q', wi)
struct_bytes += struct.pack('<Q', wv)
struct_bytes += wa.ljust(20, b'\x00')
struct_bytes += b'\x00' * 4
struct_bytes += struct.pack('<Q', amt)
assert len(struct_bytes) == 48
with open(sys.argv[1], 'wb') as f:
    f.write(struct_bytes)
    f.write(bal.to_bytes(32, 'big'))

# Expected
new_bal = bal + amt * 10**9
status = 0 if new_bal < (1 << 256) else 1
new_bal %= (1 << 256)
with open(sys.argv[2], 'wb') as f:
    f.write(struct.pack('<Q', status))
    f.write(new_bal.to_bytes(32, 'big'))
" "$in_file" "$exp_file"

  "$ZISKEMU" -e gen-out/zisk_process_withdrawal.elf \
    -i "$in_file" -o "$out_file" -n 500000 \
    >"$REPO_ROOT/gen-out/zisk_process_withdrawal_${name}.emu.log" 2>&1 || true

  local actual; actual="$(xxd -p -l 40 "$out_file" | tr -d '\n')"
  local expected; expected="$(xxd -p -l 40 "$exp_file" | tr -d '\n')"

  if [[ "$actual" == "$expected" ]]; then
    local new_bal; new_bal="$(python3 -c "print(($bal + $amt * 10**9) % (1<<256))")"
    printf "  %-30s OK   new_balance=%s\n" "$name" "${new_bal:0:24}..."
    return 0
  else
    printf "  %-30s FAIL\n    expected: %s\n    actual:   %s\n" "$name" "$expected" "$actual"
    return 1
  fi
}

ALICE="aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
ETH=$(python3 -c "print(10**18)")
GWEI=$(python3 -c "print(10**9)")

FAILED=0
# Typical mainnet withdrawal: 1 ETH = 10^9 gwei → balance += 1 ETH
run_case "one_eth_to_zero_balance" \
  1 12345 "$ALICE" "$GWEI" 0 || FAILED=1

# Existing 1 ETH balance + 32 ETH withdrawal (full validator)
run_case "32_eth_to_1_eth_balance" \
  10 100 "$ALICE" $(python3 -c "print(32 * 10**9)") "$ETH" || FAILED=1

# Zero amount: balance unchanged
run_case "zero_amount" \
  0 0 "$ALICE" 0 "$ETH" || FAILED=1

# Small amount (1 gwei): balance += 10^9
run_case "one_gwei" \
  5 50 "$ALICE" 1 0 || FAILED=1

# Large amount (max u64 gwei): balance += max_u64 × 10^9
MAX_U64=18446744073709551615
run_case "max_u64_gwei" \
  100 100 "$ALICE" "$MAX_U64" 0 || FAILED=1

# Realistic partial withdrawal: 0.5 ETH worth
run_case "half_eth" \
  3 75 "$ALICE" $(python3 -c "print(5 * 10**8)") $(python3 -c "print(100 * 10**18)") || FAILED=1

# Edge: balance already huge, add small withdrawal
HUGE_BAL=$(python3 -c "print((1 << 200))")
run_case "huge_balance_small_wd" \
  7 77 "$ALICE" 1000 "$HUGE_BAL" || FAILED=1

# Edge: amount × 10^9 + existing balance ~ 2^65 (still small relative to u256)
run_case "tiny_wd_zero_bal" \
  0 1 "$ALICE" 100 0 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: process_withdrawal credits balance with amount × 10^9"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
