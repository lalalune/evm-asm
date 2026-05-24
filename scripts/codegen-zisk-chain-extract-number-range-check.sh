#!/usr/bin/env bash
# codegen-zisk-chain-extract-number-range-check.sh -- PR-K197.
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

echo "==> emit zisk_chain_extract_number_range ELF"
lake exe codegen --program zisk_chain_extract_number_range --halt linux93 \
  -o gen-out/zisk_chain_extract_number_range

REPO_ROOT="$(pwd)"

# run_case <name> <numbers_list_py> <exp_status> <exp_min> <exp_max>
run_case() {
  local name="$1" nums="$2" exp_status="$3" exp_min="$4" exp_max="$5"

  local in_file="$REPO_ROOT/gen-out/zisk_chain_extract_number_range_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_chain_extract_number_range_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys, rlp

def u_be(n):
    if n == 0: return b''
    return n.to_bytes((n.bit_length() + 7) // 8, 'big')

def make_header(num):
    return rlp.encode([
        b'\\xa1'*32, b'\\xa2'*32, b'\\xa3'*20, b'\\xa4'*32, b'\\xa5'*32,
        b'\\xa6'*32, b'\\x00'*256, b'', u_be(num), b'\\x83\\xff\\xff\\xff',
        b'\\x82\\x02\\x00', b'\\x83\\x01\\x02\\x03', b'', b'\\xa7'*32, b'\\x00'*8,
    ])

nums = $nums
headers = [make_header(n) for n in nums]
N = len(headers)
lengths = b''.join(struct.pack('<Q', len(h)) for h in headers)
flat = b''.join(headers)

with open(sys.argv[1], 'wb') as f:
    record = struct.pack('<Q', N) + lengths + flat
    f.write(record)
    pad = (-len(record)) % 8
    if pad: f.write(b'\x00' * pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_chain_extract_number_range.elf \
    -i "$in_file" -o "$out_file" -n 5000000 \
    >"$REPO_ROOT/gen-out/zisk_chain_extract_number_range_${name}.emu.log" 2>&1 || true

  local status_le; status_le="$(xxd -p -l 8 "$out_file" | tr -d '\n')"
  local min_le;    min_le="$(   dd if="$out_file" bs=1 skip=8  count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local max_le;    max_le="$(   dd if="$out_file" bs=1 skip=16 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local status min max
  status="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$status_le'))[0])")"
  min="$(   python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$min_le'))[0])")"
  max="$(   python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$max_le'))[0])")"

  if [[ "$status" == "$exp_status" && "$min" == "$exp_min" && "$max" == "$exp_max" ]]; then
    printf "  %-26s OK   status=%s min=%s max=%s\n" "$name" "$status" "$min" "$max"
    return 0
  else
    printf "  %-26s FAIL status=%s/%s min=%s/%s max=%s/%s\n" \
      "$name" "$status" "$exp_status" "$min" "$exp_min" "$max" "$exp_max"
    return 1
  fi
}

FAILED=0
run_case "single"        "[42]"                      0 42 42 || FAILED=1
run_case "three_dense"   "[100, 101, 102]"           0 100 102 || FAILED=1
run_case "five_sparse"   "[1000, 2000, 3000, 4000, 5000]" 0 1000 5000 || FAILED=1
run_case "empty"         "[]"                        1 0 0 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: chain_extract_number_range returns the right (min, max)"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
