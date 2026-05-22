#!/usr/bin/env bash
# codegen-zisk-init-code-cost-check.sh -- PR-K107.
#
# EIP-3860 init-code gas cost = 2 * ceil(len / 32).
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

echo "==> emit zisk_init_code_cost ELF"
lake exe codegen --program zisk_init_code_cost --halt linux93 \
  -o gen-out/zisk_init_code_cost

REPO_ROOT="$(pwd)"

# run_case <name> <len> <gas_per_word>
run_case() {
  local name="$1" len="$2" gpw="$3"

  local in_file="$REPO_ROOT/gen-out/zisk_init_code_cost_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_init_code_cost_${name}.output"

  python3 -c "
import struct, sys
with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', $len))
    f.write(struct.pack('<Q', $gpw))
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_init_code_cost.elf \
    -i "$in_file" -o "$out_file" -n 1000000 \
    >"$REPO_ROOT/gen-out/zisk_init_code_cost_${name}.emu.log" 2>&1 || true

  local actual_status; actual_status="$(xxd -p -l 8 "$out_file" | tr -d '\n')"
  local actual_cost_le; actual_cost_le="$(dd if="$out_file" bs=1 skip=8 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local actual_cost; actual_cost="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$actual_cost_le'))[0])")"
  local expected; expected="$(python3 -c "print($gpw * (($len + 31) // 32))")"

  if [[ "$actual_status" == "0000000000000000" && "$actual_cost" == "$expected" ]]; then
    printf "  %-32s OK   cost=%d (len=%d)\n" "$name" "$expected" "$len"
    return 0
  else
    printf "  %-32s FAIL cost=%d expected=%d\n" "$name" "$actual_cost" "$expected"
    return 1
  fi
}

FAILED=0
# Edge cases: 0, 1, 32, 33, 64 bytes
run_case "len_0"        0      2 || FAILED=1
run_case "len_1"        1      2 || FAILED=1
run_case "len_31"       31     2 || FAILED=1
run_case "len_32"       32     2 || FAILED=1
run_case "len_33"       33     2 || FAILED=1
run_case "len_63"       63     2 || FAILED=1
run_case "len_64"       64     2 || FAILED=1
# Typical contract deploy
run_case "len_4000"     4000   2 || FAILED=1
# Max init code (EIP-3860 cap)
run_case "len_49152"    49152  2 || FAILED=1
# Custom gas_per_word
run_case "len_1024_gpw5" 1024  5 || FAILED=1
# Large len with default gpw
run_case "len_1m"       1048576 2 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: init_code_cost matches gas_per_word * ceil(len/32)"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
