#!/usr/bin/env bash
# codegen-zisk-header-extract-blob-gas-used-check.sh -- PR-K241.
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

echo "==> emit zisk_header_extract_blob_gas_used ELF"
lake exe codegen --program zisk_header_extract_blob_gas_used --halt linux93 \
  -o gen-out/zisk_header_extract_blob_gas_used

REPO_ROOT="$(pwd)"

run_case() {
  local name="$1" blob_gas_used="$2"

  local in_file="$REPO_ROOT/gen-out/zisk_header_extract_blob_gas_used_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_header_extract_blob_gas_used_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys, rlp
def u_be(n):
    if n == 0: return b''
    return n.to_bytes((n.bit_length() + 7) // 8, 'big')
g = $blob_gas_used
fields = [
    b'\\xa1'*32, b'\\xa2'*32, b'\\xa3'*20, b'\\xa4'*32, b'\\xa5'*32,
    b'\\xa6'*32, b'\\x00'*256, b'', b'\\x01', b'\\x83\\xff\\xff\\xff',
    b'', b'\\x83\\x01\\x02\\x03', b'', b'\\xa7'*32, b'\\x00'*8,
    b'\\x82\\x01\\x00', b'\\xa8'*32, u_be(g), u_be(0),
]
header_rlp = rlp.encode(fields)
with open(sys.argv[1], 'wb') as f:
    record = struct.pack('<Q', len(header_rlp)) + header_rlp
    f.write(record)
    pad = (-len(record)) % 8
    if pad: f.write(b'\x00' * pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_header_extract_blob_gas_used.elf \
    -i "$in_file" -o "$out_file" -n 1000000 \
    >"$REPO_ROOT/gen-out/zisk_header_extract_blob_gas_used_${name}.emu.log" 2>&1 || true

  local v_le; v_le="$(dd if="$out_file" bs=1 skip=8 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local actual; actual="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$v_le'))[0])")"

  if [[ "$actual" == "$blob_gas_used" ]]; then
    printf "  %-26s OK   blob_gas_used=%s\n" "$name" "$actual"
    return 0
  else
    printf "  %-26s FAIL actual=%s expected=%s\n" "$name" "$actual" "$blob_gas_used"
    return 1
  fi
}

FAILED=0
run_case "zero"          0      || FAILED=1
run_case "one_blob"      131072 || FAILED=1
run_case "six_blobs"     786432 || FAILED=1
run_case "nine_blobs"    1179648 || FAILED=1
run_case "max_u32"       4294967295 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: header_extract_blob_gas_used returns field 17"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
