#!/usr/bin/env bash
# codegen-zisk-derive-chain-id-from-v-check.sh -- PR-K37.
#
# EIP-155 split: v → (chain_id, is_eip155).
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

echo "==> emit zisk_derive_chain_id_from_v ELF"
lake exe codegen --program zisk_derive_chain_id_from_v --halt linux93 \
  -o gen-out/zisk_derive_chain_id_from_v

REPO_ROOT="$(pwd)"

run_case() {
  local name="$1" v="$2" expected_chain_id="$3" expected_is_155="$4"

  local in_file="$REPO_ROOT/gen-out/zisk_derive_chain_id_from_v_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_derive_chain_id_from_v_${name}.output"

  python3 -c "
import struct, sys
v = $v
with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', v))
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_derive_chain_id_from_v.elf \
    -i "$in_file" -o "$out_file" -n 5000 \
    >"$REPO_ROOT/gen-out/zisk_derive_chain_id_from_v_${name}.emu.log" 2>&1 || true

  local actual_chain actual_is
  actual_chain="$(xxd -p -l 8 "$out_file" 2>/dev/null | tr -d '\n')"
  actual_is="$(dd if="$out_file" bs=1 skip=8 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local exp_chain_le exp_is_le
  exp_chain_le="$(python3 -c "print(int('$expected_chain_id').to_bytes(8, 'little').hex())")"
  exp_is_le="$(python3 -c "print(int('$expected_is_155').to_bytes(8, 'little').hex())")"

  if [[ "$actual_chain" == "$exp_chain_le" && "$actual_is" == "$exp_is_le" ]]; then
    printf "  %-20s OK   v=%d chain_id=%d is_eip155=%d\n" "$name" "$v" "$expected_chain_id" "$expected_is_155"
    return 0
  else
    printf "  %-20s FAIL  v=%d\n    expected: chain=%d is=%d\n    actual:   chain=0x%s is=0x%s\n" \
      "$name" "$v" "$expected_chain_id" "$expected_is_155" "$actual_chain" "$actual_is"
    return 1
  fi
}

FAILED=0
# Pre-EIP-155
run_case "v27_pre155"   27   0     0   || FAILED=1
run_case "v28_pre155"   28   0     0   || FAILED=1
# EIP-155 chain_id 1 (mainnet): v = 35 + 2*1 = 37 or 38
run_case "v37_mainnet"  37   1     1   || FAILED=1
run_case "v38_mainnet"  38   1     1   || FAILED=1
# Chain_id 56 (BNB): v = 35 + 2*56 = 147 or 148
run_case "v147_bnb"     147  56    1   || FAILED=1
run_case "v148_bnb"     148  56    1   || FAILED=1
# Sepolia: chain_id 11155111, v = 35 + 2*11155111 = 22310257 or 22310258
run_case "v_sepolia_odd"  22310257   11155111   1   || FAILED=1
run_case "v_sepolia_even" 22310258   11155111   1   || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: derive_chain_id_from_v handles pre-EIP-155 + various chain_ids"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
