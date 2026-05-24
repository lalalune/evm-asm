#!/usr/bin/env bash
# codegen-zisk-header-extract-root-pair-check.sh -- PR-K204 + K205.
# Tests both transactions_root (field 4) and withdrawals_root (field 16).
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

run_program() {
  local prog="$1" name="$2" field_index="$3" value="$4"
  local in_file="$REPO_ROOT/gen-out/${prog}_${name}.input"
  local out_file="$REPO_ROOT/gen-out/${prog}_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys, rlp
v = bytes.fromhex('$value')
idx = $field_index
# Always emit a Shanghai-era 17-field header.
base = [
    b'\\x11'*32, b'\\x22'*32, b'\\x33'*20, b'\\x44'*32, b'\\x55'*32,
    b'\\x66'*32, b'\\x00'*256, b'', b'\\x01', b'\\x83\\xff\\xff\\xff',
    b'', b'\\x83\\x01\\x02\\x03', b'', b'\\x77'*32, b'\\x00'*8,
    b'\\x82\\x12\\x34',                # base_fee (field 15)
    b'\\x99'*32,                        # withdrawals_root (field 16)
]
base[idx] = v
header_rlp = rlp.encode(base)
with open(sys.argv[1], 'wb') as f:
    record = struct.pack('<Q', len(header_rlp)) + header_rlp
    f.write(record)
    pad = (-len(record)) % 8
    if pad: f.write(b'\x00' * pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/${prog}.elf -i "$in_file" -o "$out_file" -n 1000000 \
    >"$REPO_ROOT/gen-out/${prog}_${name}.emu.log" 2>&1 || true

  local actual; actual="$(dd if="$out_file" bs=1 skip=8 count=32 2>/dev/null | xxd -p | tr -d '\n')"
  if [[ "$actual" == "$value" ]]; then
    printf "  %-40s OK   root=%s...\n" "${prog}_${name}" "${actual:0:16}"
    return 0
  else
    printf "  %-40s FAIL actual=%s expected=%s\n" "${prog}_${name}" "$actual" "$value"
    return 1
  fi
}

REPO_ROOT="$(pwd)"
FAILED=0

echo "==> emit zisk_header_extract_transactions_root ELF"
lake exe codegen --program zisk_header_extract_transactions_root --halt linux93 \
  -o gen-out/zisk_header_extract_transactions_root
run_program "zisk_header_extract_transactions_root" "field4_matches" 4 \
  "aabbccddeeff00112233445566778899aabbccddeeff00112233445566778899" || FAILED=1

echo "==> emit zisk_header_extract_withdrawals_root ELF"
lake exe codegen --program zisk_header_extract_withdrawals_root --halt linux93 \
  -o gen-out/zisk_header_extract_withdrawals_root
run_program "zisk_header_extract_withdrawals_root" "field16_matches" 16 \
  "1234567890abcdef1234567890abcdef1234567890abcdef1234567890abcdef" || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: both transactions_root (field 4) and withdrawals_root (field 16) extractors work"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
