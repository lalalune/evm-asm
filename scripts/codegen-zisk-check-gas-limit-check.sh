#!/usr/bin/env bash
# codegen-zisk-check-gas-limit-check.sh -- PR-K72.
#
# Gas-limit continuity check per Ethereum check_gas_limit:
#   |new - parent| < parent/1024
#   new >= GAS_LIMIT_MINIMUM (5000)
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

echo "==> emit zisk_check_gas_limit ELF"
lake exe codegen --program zisk_check_gas_limit --halt linux93 \
  -o gen-out/zisk_check_gas_limit

REPO_ROOT="$(pwd)"

# run_case <name> <expected_status> <new> <parent>
run_case() {
  local name="$1" expected_status="$2" new="$3" parent="$4"

  local in_file="$REPO_ROOT/gen-out/zisk_check_gas_limit_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_check_gas_limit_${name}.output"

  python3 -c "
import struct, sys
out = struct.pack('<Q', $new) + struct.pack('<Q', $parent)
sys.stdout.buffer.write(out)
" > "$in_file"

  "$ZISKEMU" -e gen-out/zisk_check_gas_limit.elf \
    -i "$in_file" -o "$out_file" -n 500000 \
    >"$REPO_ROOT/gen-out/zisk_check_gas_limit_${name}.emu.log" 2>&1 || true

  local actual; actual="$(xxd -p -l 8 "$out_file" | tr -d '\n')"
  local exp_le; exp_le="$(python3 -c "print(int('$expected_status').to_bytes(8, 'little').hex())")"

  if [[ "$actual" == "$exp_le" ]]; then
    printf "  %-30s OK   status=%d (new=%d parent=%d)\n" "$name" "$expected_status" "$new" "$parent"
    return 0
  else
    printf "  %-30s FAIL  expected status=%d got 0x%s\n" "$name" "$expected_status" "$actual"
    return 1
  fi
}

FAILED=0
# Pass cases — new within delta and ≥ 5000
run_case "equal"               0 30000000 30000000 || FAILED=1
run_case "small_increase"      0 30000001 30000000 || FAILED=1
run_case "small_decrease"      0 29999999 30000000 || FAILED=1
run_case "just_below_delta_up" 0 30029295 30000000 || FAILED=1  # 30000000/1024 = 29296; +29295 ok (diff < delta)
run_case "just_below_delta_dn" 0 29970705 30000000 || FAILED=1  # -29295 ok
run_case "min_pass_5000"       0 5000     5000     || FAILED=1
run_case "min_pass_5001"       0 5001     5000     || FAILED=1
# Reject: min violation
run_case "below_min_4999"      1 4999     5000     || FAILED=1
run_case "below_min_zero"      1 0        30000000 || FAILED=1
# Reject: jump too far
run_case "jump_up_at_delta"    2 30029297 30000000 || FAILED=1  # at parent/1024 → fail
run_case "jump_up_above_delta" 2 30100000 30000000 || FAILED=1
run_case "jump_dn_at_delta"    2 29970704 30000000 || FAILED=1
run_case "jump_dn_far"         2 25000000 30000000 || FAILED=1
# Edge: parent < 1024 → delta = 0 → only exact-match passes
run_case "small_parent_equal"  0 5000     5000     || FAILED=1
run_case "small_parent_diff"   2 5001     5500     || FAILED=1  # delta = 5500/1024 = 5; diff = 499 > 5
# Edge: zero parent (degenerate)
run_case "zero_parent_zero_new" 1 0       0        || FAILED=1  # new=0 < 5000
# Edge: parent at MIN; delta = 5000/1024 = 4; |diff|=4 → 4 >= 4 → fail
run_case "parent_at_min_at_delta" 2 5004 5000      || FAILED=1
run_case "parent_at_min_below"   0 5003 5000      || FAILED=1  # diff=3 < delta=4 ok

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: check_gas_limit enforces |new - parent| < parent/1024 and new >= 5000"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
