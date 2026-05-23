#!/usr/bin/env bash
# codegen-zisk-bloom-or-into-check.sh -- PR-K151.
#
# In-place 256-byte bitwise OR: dst[i] |= src[i].
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

echo "==> emit zisk_bloom_or_into ELF"
lake exe codegen --program zisk_bloom_or_into --halt linux93 \
  -o gen-out/zisk_bloom_or_into

REPO_ROOT="$(pwd)"

# run_case <name> <src_hex_256B> <dst_hex_256B>
run_case() {
  local name="$1" src="$2" dst="$3"

  local in_file="$REPO_ROOT/gen-out/zisk_bloom_or_into_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_bloom_or_into_${name}.output"
  local exp_hex_file="$REPO_ROOT/gen-out/zisk_bloom_or_into_${name}.expected.hex"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys
src = bytes.fromhex('$src')
dst = bytes.fromhex('$dst')
assert len(src) == 256 and len(dst) == 256, f'sizes: src={len(src)} dst={len(dst)}'
with open(sys.argv[1], 'wb') as f:
    # 8-byte placeholder at offset 0 (ziskemu shifts user data by 8 bytes),
    # then src bloom (256 B), then dst bloom (256 B).
    f.write(struct.pack('<Q', 0))
    f.write(src + dst)
expected = bytes(s | d for s, d in zip(src, dst))
with open(sys.argv[2], 'w') as f:
    f.write(expected.hex())
" "$in_file" "$exp_hex_file"

  "$ZISKEMU" -e gen-out/zisk_bloom_or_into.elf \
    -i "$in_file" -o "$out_file" -n 100000 \
    >"$REPO_ROOT/gen-out/zisk_bloom_or_into_${name}.emu.log" 2>&1 || true

  local actual; actual="$(xxd -p -c 256 "$out_file" | tr -d '\n')"
  local expected; expected="$(cat "$exp_hex_file")"

  if [[ "$actual" == "$expected" ]]; then
    local nbits; nbits="$(python3 -c "print(bin(int('$actual', 16)).count('1'))")"
    printf "  %-30s OK   bits_set=%d\n" "$name" "$nbits"
    return 0
  else
    printf "  %-30s FAIL\n" "$name"
    printf "      actual:   %s...\n" "${actual:0:80}"
    printf "      expected: %s...\n" "${expected:0:80}"
    return 1
  fi
}

ZERO256="$(python3 -c "print('00' * 256)")"
ALL_FF256="$(python3 -c "print('ff' * 256)")"
ONES_LO="$(python3 -c "print(('80' + '00' * 7) * 32)")"  # MSB of each byte
ONES_HI="$(python3 -c "print(('01' + '00' * 7) * 32)")"

FAILED=0
# src=0, dst=0 → 0
run_case "zero_or_zero"     "$ZERO256" "$ZERO256" || FAILED=1
# src=0, dst=FF → FF
run_case "zero_or_ones"     "$ZERO256" "$ALL_FF256" || FAILED=1
# src=FF, dst=0 → FF
run_case "ones_or_zero"     "$ALL_FF256" "$ZERO256" || FAILED=1
# src=FF, dst=FF → FF
run_case "ones_or_ones"     "$ALL_FF256" "$ALL_FF256" || FAILED=1
# Disjoint bits: 0x80 high bits OR 0x01 low bits → 0x81
run_case "disjoint_bits"    "$ONES_LO" "$ONES_HI" || FAILED=1
# Random-ish patterns
RAND_A="$(python3 -c "import os; print(os.urandom(256).hex())")"
RAND_B="$(python3 -c "import os; print(os.urandom(256).hex())")"
run_case "random_a"         "$RAND_A" "$RAND_B" || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: bloom_or_into performs in-place 256-byte OR"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
