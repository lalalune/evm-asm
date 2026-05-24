#!/usr/bin/env bash
# codegen-zisk-header-extract-extra-data-check.sh -- PR-K216.
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

echo "==> emit zisk_header_extract_extra_data ELF"
lake exe codegen --program zisk_header_extract_extra_data --halt linux93 \
  -o gen-out/zisk_header_extract_extra_data

REPO_ROOT="$(pwd)"

run_case() {
  local name="$1" extra="$2" exp_status="$3" exp_len="$4" exp_bytes_hex="$5"

  local in_file="$REPO_ROOT/gen-out/zisk_header_extract_extra_data_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_header_extract_extra_data_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys, rlp
extra = '$extra'
if extra == 'over32':
    ed = b'\\xee'*40
else:
    ed = bytes.fromhex(extra) if extra else b''
fields = [
    b'\\xa1'*32, b'\\xa2'*32, b'\\xa3'*20, b'\\xa4'*32, b'\\xa5'*32,
    b'\\xa6'*32, b'\\x00'*256, b'', b'\\x01', b'\\x83\\xff\\xff\\xff',
    b'', b'\\x83\\x01\\x02\\x03', ed, b'\\xa7'*32, b'\\x00'*8,
]
header_rlp = rlp.encode(fields)
with open(sys.argv[1], 'wb') as f:
    record = struct.pack('<Q', len(header_rlp)) + header_rlp
    f.write(record)
    pad = (-len(record)) % 8
    if pad: f.write(b'\x00' * pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_header_extract_extra_data.elf \
    -i "$in_file" -o "$out_file" -n 1000000 \
    >"$REPO_ROOT/gen-out/zisk_header_extract_extra_data_${name}.emu.log" 2>&1 || true

  local status_le; status_le="$(xxd -p -l 8 "$out_file" | tr -d '\n')"
  local len_le;    len_le="$(   dd if="$out_file" bs=1 skip=8 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local status len
  status="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$status_le'))[0])")"
  len="$(   python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$len_le'))[0])")"

  if [[ "$status" != "$exp_status" || "$len" != "$exp_len" ]]; then
    printf "  %-26s FAIL status=%s/%s len=%s/%s\n" "$name" "$status" "$exp_status" "$len" "$exp_len"
    return 1
  fi
  if [[ "$exp_len" != "0" && "$exp_status" == "0" ]]; then
    local actual; actual="$(dd if="$out_file" bs=1 skip=16 count="$exp_len" 2>/dev/null | xxd -p | tr -d '\n')"
    if [[ "$actual" != "$exp_bytes_hex" ]]; then
      printf "  %-26s FAIL bytes=%s expected=%s\n" "$name" "$actual" "$exp_bytes_hex"
      return 1
    fi
  fi
  printf "  %-26s OK   status=%s len=%s\n" "$name" "$status" "$len"
  return 0
}

FAILED=0
run_case "empty"           ""        0 0  ""              || FAILED=1
run_case "short_tag"       "deadbeef" 0 4 "deadbeef"      || FAILED=1
run_case "exactly_32B"     "$(printf 'aa%.0s' {1..32})" 0 32 "$(printf 'aa%.0s' {1..32})" || FAILED=1
run_case "over_32B"        "over32"  2 0 ""               || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: header_extract_extra_data returns field 12 bytes + length"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
