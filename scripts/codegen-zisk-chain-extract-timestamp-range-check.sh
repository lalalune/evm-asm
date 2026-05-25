#!/usr/bin/env bash
# codegen-zisk-chain-extract-timestamp-range-check.sh -- PR-K239.
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

echo "==> emit zisk_chain_extract_timestamp_range ELF"
lake exe codegen --program zisk_chain_extract_timestamp_range --halt linux93 \
  -o gen-out/zisk_chain_extract_timestamp_range

REPO_ROOT="$(pwd)"

run_case() {
  local name="$1" timestamps="$2" exp_status="$3" exp_first="$4" exp_last="$5"

  local in_file="$REPO_ROOT/gen-out/zisk_chain_extract_timestamp_range_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_chain_extract_timestamp_range_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys, rlp
def u_be(n):
    if n == 0: return b''
    return n.to_bytes((n.bit_length() + 7) // 8, 'big')

def make_header(ts):
    return rlp.encode([
        b'\\xa1'*32, b'\\xa2'*32, b'\\xa3'*20, b'\\xa4'*32, b'\\xa5'*32,
        b'\\xa6'*32, b'\\x00'*256, b'', b'\\x01', b'\\x83\\xff\\xff\\xff',
        b'', u_be(ts), b'', b'\\xa7'*32, b'\\x00'*8,
    ])

vals = $timestamps
headers = [make_header(t) for t in vals]
N = len(headers)
lengths = b''.join(struct.pack('<Q', len(h)) for h in headers)
flat = b''.join(headers)
with open(sys.argv[1], 'wb') as f:
    record = struct.pack('<Q', N) + lengths + flat
    f.write(record)
    pad = (-len(record)) % 8
    if pad: f.write(b'\x00' * pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_chain_extract_timestamp_range.elf \
    -i "$in_file" -o "$out_file" -n 5000000 \
    >"$REPO_ROOT/gen-out/zisk_chain_extract_timestamp_range_${name}.emu.log" 2>&1 || true

  local s_le; s_le="$(dd if="$out_file" bs=1 skip=0  count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local f_le; f_le="$(dd if="$out_file" bs=1 skip=8  count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local l_le; l_le="$(dd if="$out_file" bs=1 skip=16 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local status first last
  status="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$s_le'))[0])")"
  first="$( python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$f_le'))[0])")"
  last="$(  python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$l_le'))[0])")"

  if [[ "$status" == "$exp_status" && "$first" == "$exp_first" && "$last" == "$exp_last" ]]; then
    printf "  %-26s OK   status=%s first=%s last=%s\n" "$name" "$status" "$first" "$last"
    return 0
  else
    printf "  %-26s FAIL status=%s/%s first=%s/%s last=%s/%s\n" "$name" "$status" "$exp_status" "$first" "$exp_first" "$last" "$exp_last"
    return 1
  fi
}

FAILED=0
run_case "empty"        "[]"                   1 0 0                  || FAILED=1
run_case "single"       "[1700000000]"         0 1700000000 1700000000 || FAILED=1
run_case "three_blocks" "[1000,1100,1200]"     0 1000 1200            || FAILED=1
run_case "large_gap"    "[1700000000,1700100000,1700200000]" 0 1700000000 1700200000 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: chain_extract_timestamp_range returns (first, last) timestamps"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
