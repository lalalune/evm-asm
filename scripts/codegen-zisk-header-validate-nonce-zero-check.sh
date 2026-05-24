#!/usr/bin/env bash
# codegen-zisk-header-validate-nonce-zero-check.sh -- PR-K218.
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

echo "==> emit zisk_header_validate_nonce_zero ELF"
lake exe codegen --program zisk_header_validate_nonce_zero --halt linux93 \
  -o gen-out/zisk_header_validate_nonce_zero

REPO_ROOT="$(pwd)"

run_case() {
  local name="$1" nonce_hex="$2" exp_valid="$3"

  local in_file="$REPO_ROOT/gen-out/zisk_header_validate_nonce_zero_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_header_validate_nonce_zero_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys, rlp
n = bytes.fromhex('$nonce_hex')
fields = [
    b'\\xa1'*32, b'\\xa2'*32, b'\\xa3'*20, b'\\xa4'*32, b'\\xa5'*32,
    b'\\xa6'*32, b'\\x00'*256, b'', b'\\x01', b'\\x83\\xff\\xff\\xff',
    b'', b'\\x83\\x01\\x02\\x03', b'', b'\\xa7'*32, n,
]
header_rlp = rlp.encode(fields)
with open(sys.argv[1], 'wb') as f:
    record = struct.pack('<Q', len(header_rlp)) + header_rlp
    f.write(record)
    pad = (-len(record)) % 8
    if pad: f.write(b'\x00' * pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_header_validate_nonce_zero.elf \
    -i "$in_file" -o "$out_file" -n 1000000 \
    >"$REPO_ROOT/gen-out/zisk_header_validate_nonce_zero_${name}.emu.log" 2>&1 || true

  local valid_le; valid_le="$(dd if="$out_file" bs=1 skip=8 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local valid; valid="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$valid_le'))[0])")"

  if [[ "$valid" == "$exp_valid" ]]; then
    printf "  %-26s OK   valid=%s\n" "$name" "$valid"
    return 0
  else
    printf "  %-26s FAIL valid=%s/%s\n" "$name" "$valid" "$exp_valid"
    return 1
  fi
}

FAILED=0
run_case "all_zero"       "0000000000000000" 1 || FAILED=1
run_case "nonzero"        "0000000000000001" 0 || FAILED=1
run_case "max_u64"        "ffffffffffffffff" 0 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: header_validate_nonce_zero enforces post-merge nonce == 0"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
