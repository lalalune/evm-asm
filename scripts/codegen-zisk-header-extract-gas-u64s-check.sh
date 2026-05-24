#!/usr/bin/env bash
# codegen-zisk-header-extract-gas-u64s-check.sh -- PR-K210 / K211.
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
v = $value
idx = $field_index
def u_be(n):
    if n == 0: return b''
    return n.to_bytes((n.bit_length() + 7) // 8, 'big')
base = [
    b'\\xa1'*32, b'\\xa2'*32, b'\\xa3'*20, b'\\xa4'*32, b'\\xa5'*32,
    b'\\xa6'*32, b'\\x00'*256, b'', b'\\x01', b'\\x83\\xff\\xff\\xff',
    b'', b'\\x83\\x01\\x02\\x03', b'', b'\\xa7'*32, b'\\x00'*8,
]
base[idx] = u_be(v)
header_rlp = rlp.encode(base)
with open(sys.argv[1], 'wb') as f:
    record = struct.pack('<Q', len(header_rlp)) + header_rlp
    f.write(record)
    pad = (-len(record)) % 8
    if pad: f.write(b'\x00' * pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/${prog}.elf -i "$in_file" -o "$out_file" -n 1000000 \
    >"$REPO_ROOT/gen-out/${prog}.emu.log" 2>&1 || true

  local v_le; v_le="$(dd if="$out_file" bs=1 skip=8 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local actual
  actual="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$v_le'))[0])")"
  if [[ "$actual" == "$value" ]]; then
    printf "  %-40s OK   value=%s\n" "$prog" "$actual"
    return 0
  else
    printf "  %-40s FAIL actual=%s expected=%s\n" "$prog" "$actual" "$value"
    return 1
  fi
}

FAILED=0
echo "==> emit zisk_header_extract_gas_used ELF"
lake exe codegen --program zisk_header_extract_gas_used --halt linux93 \
  -o gen-out/zisk_header_extract_gas_used
run_program "zisk_header_extract_gas_used" 10 12345678 || FAILED=1

echo "==> emit zisk_header_extract_gas_limit ELF"
lake exe codegen --program zisk_header_extract_gas_limit --halt linux93 \
  -o gen-out/zisk_header_extract_gas_limit
run_program "zisk_header_extract_gas_limit" 9 30000000 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: gas_used / gas_limit u64 extractors match"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
