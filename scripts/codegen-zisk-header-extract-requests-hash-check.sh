#!/usr/bin/env bash
# codegen-zisk-header-extract-requests-hash-check.sh -- PR-K283.
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

echo "==> emit zisk_header_extract_requests_hash ELF"
lake exe codegen --program zisk_header_extract_requests_hash --halt linux93 \
  -o gen-out/zisk_header_extract_requests_hash

REPO_ROOT="$(pwd)"

run_case() {
  local name="$1" fields_count="$2" rh_hex="$3" exp_status="$4" exp_rh_hex="$5"

  local in_file="$REPO_ROOT/gen-out/zisk_header_extract_requests_hash_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_header_extract_requests_hash_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys, rlp
fields_count = $fields_count
rh_hex = '$rh_hex'
rh = bytes.fromhex(rh_hex) if rh_hex else b''
all_fields = [
    b'\\xa1'*32, b'\\xa2'*32, b'\\xa3'*20, b'\\xa4'*32, b'\\xa5'*32,
    b'\\xa6'*32, b'\\x00'*256, b'', b'\\x01', b'\\x83\\xff\\xff\\xff',
    b'', b'\\x83\\x01\\x02\\x03', b'', b'\\xa7'*32, b'\\x00'*8,
    b'\\x84\\x05\\xf5\\xe1\\x00', b'\\xa8'*32, b'',
    b'\\x83\\x00\\x10\\x00', b'\\xab'*32, rh,
][:fields_count]
header = rlp.encode(all_fields)
with open(sys.argv[1], 'wb') as f:
    record = struct.pack('<Q', len(header)) + header
    f.write(record)
    pad = (-len(record)) % 8
    if pad: f.write(b'\\x00' * pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_header_extract_requests_hash.elf \
    -i "$in_file" -o "$out_file" -n 5000000 \
    >"$REPO_ROOT/gen-out/zisk_header_extract_requests_hash_${name}.emu.log" 2>&1 || true

  local s_le; s_le="$(dd if="$out_file" bs=1 skip=0 count=8  2>/dev/null | xxd -p | tr -d '\n')"
  local actual_rh; actual_rh="$(dd if="$out_file" bs=1 skip=8 count=32 2>/dev/null | xxd -p | tr -d '\n')"
  local status
  status="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$s_le'))[0])")"

  if [[ "$status" == "$exp_status" && "$actual_rh" == "$exp_rh_hex" ]]; then
    printf "  %-32s OK   status=%s\n" "$name" "$status"
    return 0
  else
    printf "  %-32s FAIL status=%s/%s rh=%s/%s\n" "$name" "$status" "$exp_status" "$actual_rh" "$exp_rh_hex"
    return 1
  fi
}

ZERO32="$(python3 -c "print('00'*32)")"
NONZERO="$(python3 -c "print('dd'*32)")"
MIXED="$(python3 -c "print('22'*16 + 'ee'*16)")"

FAILED=0
run_case "zero_rh"             21 "$ZERO32"  0 "$ZERO32"  || FAILED=1
run_case "nonzero_rh"          21 "$NONZERO" 0 "$NONZERO" || FAILED=1
run_case "mixed_rh"            21 "$MIXED"   0 "$MIXED"   || FAILED=1
run_case "pre_prague_20"       20 "$ZERO32"  1 "$ZERO32"  || FAILED=1
run_case "pre_prague_15"       15 "$ZERO32"  1 "$ZERO32"  || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: header_extract_requests_hash reads field 20"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
