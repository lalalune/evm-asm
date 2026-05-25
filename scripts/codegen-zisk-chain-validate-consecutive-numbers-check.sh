#!/usr/bin/env bash
# codegen-zisk-chain-validate-consecutive-numbers-check.sh -- PR-K230.
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

echo "==> emit zisk_chain_validate_consecutive_numbers ELF"
lake exe codegen --program zisk_chain_validate_consecutive_numbers --halt linux93 \
  -o gen-out/zisk_chain_validate_consecutive_numbers

REPO_ROOT="$(pwd)"

run_case() {
  local name="$1" nums="$2" exp_valid="$3" exp_bad="$4"

  local in_file="$REPO_ROOT/gen-out/zisk_chain_validate_consecutive_numbers_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_chain_validate_consecutive_numbers_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys, rlp
def u_be(n):
    if n == 0: return b''
    return n.to_bytes((n.bit_length() + 7) // 8, 'big')
def make_header(num):
    return rlp.encode([
        b'\\xa1'*32, b'\\xa2'*32, b'\\xa3'*20, b'\\xa4'*32, b'\\xa5'*32,
        b'\\xa6'*32, b'\\x00'*256, b'', u_be(num), b'\\x83\\xff\\xff\\xff',
        b'', b'\\x83\\x01\\x02\\x03', b'', b'\\xa7'*32, b'\\x00'*8,
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

  "$ZISKEMU" -e gen-out/zisk_chain_validate_consecutive_numbers.elf \
    -i "$in_file" -o "$out_file" -n 5000000 \
    >"$REPO_ROOT/gen-out/zisk_chain_validate_consecutive_numbers_${name}.emu.log" 2>&1 || true

  local v_le; v_le="$(dd if="$out_file" bs=1 skip=8  count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local b_le; b_le="$(dd if="$out_file" bs=1 skip=16 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local valid; valid="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$v_le'))[0])")"
  local bad;   bad="$(  python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$b_le'))[0])")"

  if [[ "$valid" == "$exp_valid" && "$bad" == "$exp_bad" ]]; then
    printf "  %-26s OK   valid=%s bad=%s\n" "$name" "$valid" "$bad"
    return 0
  else
    printf "  %-26s FAIL valid=%s/%s bad=%s/%s\n" "$name" "$valid" "$exp_valid" "$bad" "$exp_bad"
    return 1
  fi
}

FAILED=0
run_case "vacuous_empty"  "[]" 1 0 || FAILED=1
run_case "vacuous_single" "[100]" 1 0 || FAILED=1
run_case "consecutive"    "[100,101,102]" 1 0 || FAILED=1
run_case "skip_at_2"      "[100,101,103]" 0 2 || FAILED=1
run_case "decreasing"     "[100,99,98]"   0 1 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: chain_validate_consecutive_numbers enforces number[i+1]==number[i]+1"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
