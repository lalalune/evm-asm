#!/usr/bin/env bash
# codegen-zisk-header-extract-ommers-prev-randao-check.sh -- PR-K206 + K207.
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

REPO_ROOT="$(pwd)"

run_program() {
  local prog="$1" field_index="$2" value="$3"
  local in_file="$REPO_ROOT/gen-out/${prog}.input"
  local out_file="$REPO_ROOT/gen-out/${prog}.output"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys, rlp
v = bytes.fromhex('$value')
idx = $field_index
base = [
    b'\\x11'*32, b'\\x22'*32, b'\\x33'*20, b'\\x44'*32, b'\\x55'*32,
    b'\\x66'*32, b'\\x00'*256, b'', b'\\x01', b'\\x83\\xff\\xff\\xff',
    b'', b'\\x83\\x01\\x02\\x03', b'', b'\\x77'*32, b'\\x00'*8,
    b'\\x82\\x12\\x34', b'\\x99'*32,
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
    >"$REPO_ROOT/gen-out/${prog}.emu.log" 2>&1 || true

  local actual; actual="$(dd if="$out_file" bs=1 skip=8 count=32 2>/dev/null | xxd -p | tr -d '\n')"
  if [[ "$actual" == "$value" ]]; then
    printf "  %-44s OK   field=%s...\n" "$prog" "${actual:0:16}"
    return 0
  else
    printf "  %-44s FAIL actual=%s expected=%s\n" "$prog" "$actual" "$value"
    return 1
  fi
}

FAILED=0
echo "==> emit zisk_header_extract_ommers_hash ELF"
lake exe codegen --program zisk_header_extract_ommers_hash --halt linux93 \
  -o gen-out/zisk_header_extract_ommers_hash
run_program "zisk_header_extract_ommers_hash" 1 \
  "1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347" || FAILED=1

echo "==> emit zisk_header_extract_prev_randao ELF"
lake exe codegen --program zisk_header_extract_prev_randao --halt linux93 \
  -o gen-out/zisk_header_extract_prev_randao
run_program "zisk_header_extract_prev_randao" 13 \
  "deadbeefcafe1234deadbeefcafe1234deadbeefcafe1234deadbeefcafe1234" || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: ommers_hash (field 1) and prev_randao (field 13) extractors match"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
