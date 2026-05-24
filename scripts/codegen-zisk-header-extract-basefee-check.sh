#!/usr/bin/env bash
# codegen-zisk-header-extract-basefee-check.sh -- PR-K198.
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

echo "==> emit zisk_header_extract_basefee ELF"
lake exe codegen --program zisk_header_extract_basefee --halt linux93 \
  -o gen-out/zisk_header_extract_basefee

REPO_ROOT="$(pwd)"

# run_case <name> <basefee_int_or_-1> <pre_london 0/1> <exp_status> <exp_basefee>
run_case() {
  local name="$1" bf="$2" pre_london="$3" exp_status="$4" exp_basefee="$5"

  local in_file="$REPO_ROOT/gen-out/zisk_header_extract_basefee_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_header_extract_basefee_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys, rlp

def u_be(n):
    if n == 0: return b''
    return n.to_bytes((n.bit_length() + 7) // 8, 'big')

bf = $bf
pre_london = $pre_london == 1

# Pre-London = 15 fields, no base_fee. London+ = 16 fields with base_fee.
base_fields = [
    b'\\xa1'*32, b'\\xa2'*32, b'\\xa3'*20, b'\\xa4'*32, b'\\xa5'*32,
    b'\\xa6'*32, b'\\x00'*256, b'', b'\\x01', b'\\x83\\xff\\xff\\xff',
    b'', b'\\x83\\x01\\x02\\x03', b'', b'\\xa7'*32, b'\\x00'*8,
]
if pre_london:
    header_rlp = rlp.encode(base_fields)
else:
    header_rlp = rlp.encode(base_fields + [u_be(bf)])

with open(sys.argv[1], 'wb') as f:
    record = struct.pack('<Q', len(header_rlp)) + header_rlp
    f.write(record)
    pad = (-len(record)) % 8
    if pad: f.write(b'\x00' * pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_header_extract_basefee.elf \
    -i "$in_file" -o "$out_file" -n 1000000 \
    >"$REPO_ROOT/gen-out/zisk_header_extract_basefee_${name}.emu.log" 2>&1 || true

  local status_le; status_le="$(xxd -p -l 8 "$out_file" | tr -d '\n')"
  local bf_le;     bf_le="$(   dd if="$out_file" bs=1 skip=8 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local status basefee
  status="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$status_le'))[0])")"
  basefee="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$bf_le'))[0])")"

  if [[ "$status" == "$exp_status" && "$basefee" == "$exp_basefee" ]]; then
    printf "  %-26s OK   status=%s base_fee=%s\n" "$name" "$status" "$basefee"
    return 0
  else
    printf "  %-26s FAIL status=%s/%s base_fee=%s/%s\n" \
      "$name" "$status" "$exp_status" "$basefee" "$exp_basefee"
    return 1
  fi
}

FAILED=0
run_case "london_30_gwei"   "$((30 * 10**9))"  0 0 30000000000 || FAILED=1
run_case "london_zero"      "0"                 0 0 0           || FAILED=1
run_case "london_1234"      "1234"              0 0 1234        || FAILED=1
run_case "pre_london"       "-1"                1 1 0           || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: header_extract_basefee returns the right field 15 value"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
