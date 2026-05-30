#!/usr/bin/env bash
# codegen-zisk-witness-state-keccak-at-index-check.sh
#
# Index -> keccak primitive: read entry i of witness.state
# and return keccak256(entry).
#
# Output (40 bytes):
#   bytes  0.. 8 : status (0=ok, 1=OOB)
#   bytes  8..40 : keccak256 hash (zero on OOB)
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

echo "==> emit zisk_witness_state_keccak_at_index ELF"
lake exe codegen --program zisk_witness_state_keccak_at_index \
  --halt linux93 \
  -o gen-out/zisk_witness_state_keccak_at_index

REPO_ROOT="$(pwd)"

run_case() {
  local name="$1"; shift
  local mode="$1"; shift
  local idx="$1"; shift

  local in_file="$REPO_ROOT/gen-out/zisk_wski_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_wski_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_wski_${name}.expected"

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

if mode == 'single_entry':
    entries = [b'one-entry-payload']
elif mode == 'three_entries':
    entries = [b'first', b'second-entry', b'third-very-long-entry-data-12345678']
elif mode == 'empty':
    entries = []
else:
    raise SystemExit('bad mode: ' + mode)

witness_state = build_ssz_section(entries)

if idx < len(entries):
    walked = k256(entries[idx])
    expected = struct.pack('<Q', 0) + walked
else:
    expected = struct.pack('<Q', 1) + b'\\x00' * 32

with open(sys.argv[1], 'wb') as f:
    record = (
        struct.pack('<Q', len(witness_state))
        + struct.pack('<Q', idx)
        + witness_state
    )
    f.write(record)
    pad = (-len(record)) % 8
    if pad: f.write(b'\\x00' * pad)

with open(sys.argv[2], 'wb') as f:
    f.write(expected)
" "$in_file" "$exp_file"

  "$ZISKEMU" -e gen-out/zisk_witness_state_keccak_at_index.elf \
    -i "$in_file" -o "$out_file" -n 4000000 \
    >"$REPO_ROOT/gen-out/zisk_wski_${name}.emu.log" 2>&1 || true

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
# 1) Single-entry section, index 0 -> keccak of the only entry.
run_case "single_idx0"                   single_entry  0 || FAILED=1
# 2) Three entries, index 0 (first).
run_case "three_idx0_first"              three_entries 0 || FAILED=1
# 3) Three entries, index 1 (middle).
run_case "three_idx1_middle"             three_entries 1 || FAILED=1
# 4) Three entries, index 2 (last, exercises the section_end branch).
run_case "three_idx2_last"               three_entries 2 || FAILED=1
# 5) Three entries, index 3 -> OOB (status=1, zero hash).
run_case "three_idx3_oob"                three_entries 3 || FAILED=1
# 6) Empty section, index 0 -> OOB.
run_case "empty_section_idx0_oob"        empty         0 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: witness_state_keccak_at_index end-to-end"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
