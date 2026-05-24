#!/usr/bin/env bash
# codegen-zisk-header-extract-difficulty-check.sh -- PR-K215.
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

echo "==> emit zisk_header_extract_difficulty ELF"
lake exe codegen --program zisk_header_extract_difficulty --halt linux93 \
  -o gen-out/zisk_header_extract_difficulty

REPO_ROOT="$(pwd)"

run_case() {
  local name="$1" diff="$2"

  local in_file="$REPO_ROOT/gen-out/zisk_header_extract_difficulty_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_header_extract_difficulty_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys, rlp
def u_be(n):
    if n == 0: return b''
    return n.to_bytes((n.bit_length() + 7) // 8, 'big')
d = $diff
fields = [
    b'\\xa1'*32, b'\\xa2'*32, b'\\xa3'*20, b'\\xa4'*32, b'\\xa5'*32,
    b'\\xa6'*32, b'\\x00'*256, u_be(d), b'\\x01', b'\\x83\\xff\\xff\\xff',
    b'', b'\\x83\\x01\\x02\\x03', b'', b'\\xa7'*32, b'\\x00'*8,
]
header_rlp = rlp.encode(fields)
with open(sys.argv[1], 'wb') as f:
    record = struct.pack('<Q', len(header_rlp)) + header_rlp
    f.write(record)
    pad = (-len(record)) % 8
    if pad: f.write(b'\x00' * pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_header_extract_difficulty.elf \
    -i "$in_file" -o "$out_file" -n 1000000 \
    >"$REPO_ROOT/gen-out/zisk_header_extract_difficulty_${name}.emu.log" 2>&1 || true

  local v_le; v_le="$(dd if="$out_file" bs=1 skip=8 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local actual; actual="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$v_le'))[0])")"

  if [[ "$actual" == "$diff" ]]; then
    printf "  %-26s OK   difficulty=%s\n" "$name" "$actual"
    return 0
  else
    printf "  %-26s FAIL actual=%s expected=%s\n" "$name" "$actual" "$diff"
    return 1
  fi
}

FAILED=0
run_case "post_merge_zero"  0          || FAILED=1
run_case "pre_merge_typical" 1000000000 || FAILED=1
run_case "small"             42         || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: header_extract_difficulty returns field 7"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
