#!/usr/bin/env bash
# codegen-zisk-calc-excess-blob-gas-check.sh -- PR-K63.
#
# EIP-4844 excess_blob_gas calculation:
#   max(0, parent.excess_blob_gas + parent.blob_gas_used - target)
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

echo "==> emit zisk_calc_excess_blob_gas ELF"
lake exe codegen --program zisk_calc_excess_blob_gas --halt linux93 \
  -o gen-out/zisk_calc_excess_blob_gas

REPO_ROOT="$(pwd)"

# run_case <name> <parent_excess> <parent_used> <target>
run_case() {
  local name="$1" parent_excess="$2" parent_used="$3" target="$4"

  local in_file="$REPO_ROOT/gen-out/zisk_calc_excess_blob_gas_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_calc_excess_blob_gas_${name}.output"

  python3 -c "
import struct, sys
out = struct.pack('<Q', $parent_excess)
out += struct.pack('<Q', $parent_used)
out += struct.pack('<Q', $target)
sys.stdout.buffer.write(out)
" > "$in_file"

  "$ZISKEMU" -e gen-out/zisk_calc_excess_blob_gas.elf \
    -i "$in_file" -o "$out_file" -n 500000 \
    >"$REPO_ROOT/gen-out/zisk_calc_excess_blob_gas_${name}.emu.log" 2>&1 || true

  local expected; expected="$(python3 -c "
pe, pu, t = $parent_excess, $parent_used, $target
total = pe + pu
print(0 if total < t else (total - t))
")"
  local actual; actual="$(python3 -c "
with open('$out_file', 'rb') as f:
    raw = f.read()[:8]
print(int.from_bytes(raw, 'little'))
")"

  if [[ "$actual" == "$expected" ]]; then
    printf "  %-30s OK   result=%d\n" "$name" "$expected"
    return 0
  else
    printf "  %-30s FAIL  expected %d got %d\n" "$name" "$expected" "$actual"
    return 1
  fi
}

CANCUN_TARGET=393216           # 3 blobs × 131072
PRAGUE_TARGET=786432           # 6 blobs × 131072 (EIP-7691 candidate)
GAS_PER_BLOB=131072

FAILED=0
# Sum below target → 0
run_case "below_target_zero"     0           0           "$CANCUN_TARGET" || FAILED=1
run_case "below_target_small"    100         200         "$CANCUN_TARGET" || FAILED=1
run_case "exactly_target"        0           "$CANCUN_TARGET" "$CANCUN_TARGET" || FAILED=1   # sum=target → 0
run_case "exactly_target_split"  "$GAS_PER_BLOB" $((2 * GAS_PER_BLOB)) "$CANCUN_TARGET" || FAILED=1
# Above target → positive diff
run_case "above_target_small"    "$CANCUN_TARGET" 1     "$CANCUN_TARGET" || FAILED=1
run_case "double_target"         "$CANCUN_TARGET" "$CANCUN_TARGET" "$CANCUN_TARGET" || FAILED=1
run_case "much_higher"           5000000     0           "$CANCUN_TARGET" || FAILED=1
# Realistic: parent block consumed 4 blobs (over target by 1 blob)
run_case "parent_4_blobs"        0           $((4 * GAS_PER_BLOB)) "$CANCUN_TARGET" || FAILED=1
# Realistic: parent had 2 blobs (under target by 1)
run_case "parent_2_blobs"        500000      $((2 * GAS_PER_BLOB)) "$CANCUN_TARGET" || FAILED=1
# Prague-era larger target
run_case "prague_below_target"   "$CANCUN_TARGET" 0     "$PRAGUE_TARGET" || FAILED=1
run_case "prague_above_target"   "$PRAGUE_TARGET" "$PRAGUE_TARGET" "$PRAGUE_TARGET" || FAILED=1
# Edge: only parent_excess set
run_case "only_excess"           1000        0           "$CANCUN_TARGET" || FAILED=1
# Edge: only parent_used set
run_case "only_used"             0           "$CANCUN_TARGET" "$CANCUN_TARGET" || FAILED=1
# Edge: target = 0 (degenerate but allowed)
run_case "target_zero"           100         200         0           || FAILED=1
# Steady state typical: small excess, fewer blobs than target
run_case "steady_state"          1000        $((1 * GAS_PER_BLOB)) "$CANCUN_TARGET" || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: calc_excess_blob_gas matches max(0, parent_excess + parent_used - target)"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
