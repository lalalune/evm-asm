#!/usr/bin/env bash
# codegen-zisk-intrinsic-gas-legacy-check.sh -- PR-K46.
#
# Validate the base + creation + EIP-2028 data gas formula:
#   gas = 21000
#       + (32000 if creation else 0)
#       + sum(4 if b == 0 else 16 for b in data)
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

echo "==> emit zisk_intrinsic_gas_legacy ELF"
lake exe codegen --program zisk_intrinsic_gas_legacy --halt linux93 \
  -o gen-out/zisk_intrinsic_gas_legacy

REPO_ROOT="$(pwd)"

# run_case <name> <is_creation 0|1> <data_hex>
run_case() {
  local name="$1" is_creation="$2" data_hex="$3"

  local in_file="$REPO_ROOT/gen-out/zisk_intrinsic_gas_legacy_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_intrinsic_gas_legacy_${name}.output"

  python3 -c "
import struct, sys
data = bytes.fromhex('$data_hex')
is_creation = $is_creation
out  = struct.pack('<Q', len(data))
out += struct.pack('<Q', is_creation)
out += data
pad = (-(16 + len(data))) % 8
if pad:
    out += b'\x00' * pad
sys.stdout.buffer.write(out)
" > "$in_file"

  "$ZISKEMU" -e gen-out/zisk_intrinsic_gas_legacy.elf \
    -i "$in_file" -o "$out_file" -n 500000 \
    >"$REPO_ROOT/gen-out/zisk_intrinsic_gas_legacy_${name}.emu.log" 2>&1 || true

  local expected; expected="$(python3 -c "
data = bytes.fromhex('$data_hex')
is_creation = $is_creation
gas = 21000
if is_creation:
    gas += 32000
for b in data:
    gas += 4 if b == 0 else 16
print(gas)
")"
  local actual; actual="$(python3 -c "
with open('$out_file', 'rb') as f:
    raw = f.read()[:8]
print(int.from_bytes(raw, 'little'))
")"

  if [[ "$actual" == "$expected" ]]; then
    printf "  %-30s OK   gas=%d (data_len=%d, creation=%d)\n" \
      "$name" "$expected" "$((${#data_hex} / 2))" "$is_creation"
    return 0
  else
    printf "  %-30s FAIL  expected gas=%d got %d\n" "$name" "$expected" "$actual"
    return 1
  fi
}

FAILED=0
# Empty data
run_case "empty_call"                 0 ""                                 || FAILED=1
run_case "empty_creation"             1 ""                                 || FAILED=1
# Single byte
run_case "one_zero_call"              0 "00"                               || FAILED=1
run_case "one_nonzero_call"           0 "ff"                               || FAILED=1
run_case "one_zero_creation"          1 "00"                               || FAILED=1
run_case "one_nonzero_creation"       1 "ff"                               || FAILED=1
# Mixed
run_case "mixed_data"                 0 "0011002200330044005500"           || FAILED=1
# 32 bytes of zeros
run_case "32_zeros"                   0 "$(printf '00%.0s' $(seq 1 32))"   || FAILED=1
# 32 bytes of nonzeros
run_case "32_nonzeros"                0 "$(printf 'ff%.0s' $(seq 1 32))"   || FAILED=1
# Typical 4-byte selector + 32-byte arg (all nonzero high bytes)
run_case "selector_plus_arg"          0 "a9059cbb000000000000000000000000aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa00000000000000000000000000000000000000000000000000000000000003e8" || FAILED=1
# Creation with bytecode-like payload
run_case "creation_with_bytecode"     1 "6080604052348015600f57600080fd5b50603f80601d6000396000f3" || FAILED=1
# Large blob (1024 bytes of pseudo-random)
LARGE_DATA="$(python3 -c "print(bytes((i * 31 + 7) & 0xff for i in range(1024)).hex())")"
run_case "large_1024B"                0 "$LARGE_DATA"                      || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: intrinsic_gas_legacy matches base + creation + EIP-2028 data formula"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
