#!/usr/bin/env bash
# codegen-zisk-header-extract-parent-hash-check.sh -- PR-K202.
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

echo "==> emit zisk_header_extract_parent_hash ELF"
lake exe codegen --program zisk_header_extract_parent_hash --halt linux93 \
  -o gen-out/zisk_header_extract_parent_hash

REPO_ROOT="$(pwd)"

run_case() {
  local name="$1" ph="$2" exp_status="$3" exp_hash="$4"

  local in_file="$REPO_ROOT/gen-out/zisk_header_extract_parent_hash_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_header_extract_parent_hash_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys, rlp
ph = '$ph'
if ph == 'garbage':
    header_rlp = b'\\x00'
else:
    if ph == 'short':
        parent = b'\\xaa'*16
    else:
        parent = bytes.fromhex(ph)
    fields = [
        parent, b'\\x22'*32, b'\\x33'*20, b'\\x44'*32, b'\\x55'*32,
        b'\\x66'*32, b'\\x00'*256, b'', b'\\x01', b'\\x83\\xff\\xff\\xff',
        b'', b'\\x83\\x01\\x02\\x03', b'', b'\\x77'*32, b'\\x00'*8,
    ]
    header_rlp = rlp.encode(fields)
with open(sys.argv[1], 'wb') as f:
    record = struct.pack('<Q', len(header_rlp)) + header_rlp
    f.write(record)
    pad = (-len(record)) % 8
    if pad: f.write(b'\x00' * pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_header_extract_parent_hash.elf \
    -i "$in_file" -o "$out_file" -n 1000000 \
    >"$REPO_ROOT/gen-out/zisk_header_extract_parent_hash_${name}.emu.log" 2>&1 || true

  local status_le; status_le="$(xxd -p -l 8 "$out_file" | tr -d '\n')"
  local actual; actual="$(dd if="$out_file" bs=1 skip=8 count=32 2>/dev/null | xxd -p | tr -d '\n')"
  local status
  status="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$status_le'))[0])")"

  if [[ "$status" == "$exp_status" && "$actual" == "$exp_hash" ]]; then
    printf "  %-26s OK   status=%s hash=%s...\n" "$name" "$status" "${actual:0:16}"
    return 0
  else
    printf "  %-26s FAIL status=%s/%s hash=%s/%s\n" \
      "$name" "$status" "$exp_status" "$actual" "$exp_hash"
    return 1
  fi
}

ZERO="0000000000000000000000000000000000000000000000000000000000000000"

FAILED=0
run_case "match_typical"   "abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789" 0 "abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789" || FAILED=1
run_case "match_zero"      "$ZERO"   0 "$ZERO"   || FAILED=1
run_case "fail_short"      "short"   2 "$ZERO"   || FAILED=1
run_case "fail_garbage"    "garbage" 1 "$ZERO"   || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: header_extract_parent_hash copies field 0 to output"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
