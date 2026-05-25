#!/usr/bin/env bash
# codegen-zisk-chain-extract-first-last-beneficiary-check.sh -- PR-K256.
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

echo "==> emit zisk_chain_extract_first_last_beneficiary ELF"
lake exe codegen --program zisk_chain_extract_first_last_beneficiary --halt linux93 \
  -o gen-out/zisk_chain_extract_first_last_beneficiary

REPO_ROOT="$(pwd)"

run_case() {
  local name="$1" bens_hex="$2" exp_status="$3" exp_first_hex="$4" exp_last_hex="$5"

  local in_file="$REPO_ROOT/gen-out/zisk_chain_extract_first_last_beneficiary_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_chain_extract_first_last_beneficiary_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys, rlp

def make_header(ben_hex):
    return rlp.encode([
        b'\\xa1'*32, b'\\xa2'*32, bytes.fromhex(ben_hex), b'\\xa4'*32, b'\\xa5'*32,
        b'\\xa6'*32, b'\\x00'*256, b'', b'\\x01', b'\\x83\\xff\\xff\\xff',
        b'', b'\\x83\\x01\\x02\\x03', b'', b'\\xa7'*32, b'\\x00'*8,
    ])

bens = $bens_hex
headers = [make_header(b) for b in bens]
N = len(headers)
lengths = b''.join(struct.pack('<Q', len(h)) for h in headers)
flat = b''.join(headers)
with open(sys.argv[1], 'wb') as f:
    record = struct.pack('<Q', N) + lengths + flat
    f.write(record)
    pad = (-len(record)) % 8
    if pad: f.write(b'\x00' * pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_chain_extract_first_last_beneficiary.elf \
    -i "$in_file" -o "$out_file" -n 5000000 \
    >"$REPO_ROOT/gen-out/zisk_chain_extract_first_last_beneficiary_${name}.emu.log" 2>&1 || true

  local s_le; s_le="$(dd if="$out_file" bs=1 skip=0  count=8  2>/dev/null | xxd -p | tr -d '\n')"
  local fr_hex; fr_hex="$(dd if="$out_file" bs=1 skip=8  count=20 2>/dev/null | xxd -p | tr -d '\n')"
  local lr_hex; lr_hex="$(dd if="$out_file" bs=1 skip=32 count=20 2>/dev/null | xxd -p | tr -d '\n')"
  local status
  status="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$s_le'))[0])")"

  if [[ "$status" == "$exp_status" && "$fr_hex" == "$exp_first_hex" && "$lr_hex" == "$exp_last_hex" ]]; then
    printf "  %-26s OK   status=%s first=%s.. last=%s..\n" "$name" "$status" "${fr_hex:0:16}" "${lr_hex:0:16}"
    return 0
  else
    printf "  %-26s FAIL status=%s/%s first=%s/%s last=%s/%s\n" "$name" "$status" "$exp_status" "$fr_hex" "$exp_first_hex" "$lr_hex" "$exp_last_hex"
    return 1
  fi
}

ZERO20="$(printf '0%.0s' {1..40})"
HEAD1="$(printf '11%.0s' {1..20})"
HEAD2="$(printf '22%.0s' {1..20})"
HEAD3="$(printf '33%.0s' {1..20})"

FAILED=0
run_case "empty"       "[]"                    1 "$ZERO20" "$ZERO20" || FAILED=1
run_case "single"      "['$HEAD1']"            0 "$HEAD1"  "$HEAD1"  || FAILED=1
run_case "two"         "['$HEAD1', '$HEAD2']"  0 "$HEAD1"  "$HEAD2"  || FAILED=1
run_case "three"       "['$HEAD1', '$HEAD2', '$HEAD3']" 0 "$HEAD1" "$HEAD3" || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: chain_extract_first_last_beneficiary returns (first, last) beneficiary"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
