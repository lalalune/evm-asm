#!/usr/bin/env bash
# codegen-zisk-witness-codes-keccak-at-index-check.sh
#
# Index -> keccak over witness.codes. Returns the
# canonical code_hash of the i-th deployed bytecode.
#
# Output (40 bytes):
#   bytes  0.. 8 : status (0=ok, 1=OOB)
#   bytes  8..40 : keccak256 / code_hash (32 B; zero on OOB)
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

echo "==> emit zisk_witness_codes_keccak_at_index ELF"
lake exe codegen --program zisk_witness_codes_keccak_at_index \
  --halt linux93 \
  -o gen-out/zisk_witness_codes_keccak_at_index

REPO_ROOT="$(pwd)"

run_case() {
  local name="$1"; shift
  local mode="$1"; shift
  local idx="$1"; shift

  local in_file="$REPO_ROOT/gen-out/zisk_wcki_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_wcki_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_wcki_${name}.expected"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys
from Crypto.Hash import keccak

def k256(b):
    h = keccak.new(digest_bits=256); h.update(b); return h.digest()

def build_ssz_section(elements):
    n = len(elements)
    if n == 0: return b''
    section = b''
    offset = 4 * n
    for e in elements:
        section += struct.pack('<I', offset); offset += len(e)
    for e in elements: section += e
    return section

mode = '$mode'
idx = int('$idx')

if mode == 'single':
    bytecodes = [bytes.fromhex('600160005500')]
elif mode == 'three_contracts':
    bytecodes = [
        bytes.fromhex('6000'),
        bytes.fromhex('600160005500'),
        bytes.fromhex('60ff60005260206000f3'),
    ]
elif mode == 'empty':
    bytecodes = []
else:
    raise SystemExit('bad mode')

witness_codes = build_ssz_section(bytecodes)

if idx < len(bytecodes):
    expected = struct.pack('<Q', 0) + k256(bytecodes[idx])
else:
    expected = struct.pack('<Q', 1) + b'\\x00' * 32

with open(sys.argv[1], 'wb') as f:
    record = (
        struct.pack('<Q', len(witness_codes))
        + struct.pack('<Q', idx)
        + witness_codes
    )
    f.write(record)
    pad = (-len(record)) % 8
    if pad: f.write(b'\\x00' * pad)

with open(sys.argv[2], 'wb') as f:
    f.write(expected)
" "$in_file" "$exp_file"

  "$ZISKEMU" -e gen-out/zisk_witness_codes_keccak_at_index.elf \
    -i "$in_file" -o "$out_file" -n 4000000 \
    >"$REPO_ROOT/gen-out/zisk_wcki_${name}.emu.log" 2>&1 || true

  local exp_size
  exp_size="$(stat -c%s "$exp_file")"
  local actual expected
  actual="$(xxd -p -l "$exp_size" "$out_file" 2>/dev/null | tr -d '\n')"
  expected="$(xxd -p -l "$exp_size" "$exp_file" 2>/dev/null | tr -d '\n')"

  if [[ "$actual" == "$expected" ]]; then
    printf "  %-40s OK   %d bytes match\n" "$name" "$exp_size"
    return 0
  else
    printf "  %-40s FAIL\n    expected: %s\n    actual:   %s\n" \
      "$name" "$expected" "$actual"
    return 1
  fi
}

FAILED=0
run_case "single_idx0"                   single 0 || FAILED=1
run_case "three_idx0_first"              three_contracts 0 || FAILED=1
run_case "three_idx1_middle"             three_contracts 1 || FAILED=1
run_case "three_idx2_last"               three_contracts 2 || FAILED=1
run_case "three_idx3_oob"                three_contracts 3 || FAILED=1
run_case "empty_section_oob"             empty 0 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: witness_codes_keccak_at_index end-to-end"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
