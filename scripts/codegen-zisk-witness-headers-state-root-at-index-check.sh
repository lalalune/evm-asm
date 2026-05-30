#!/usr/bin/env bash
# codegen-zisk-witness-headers-state-root-at-index-check.sh
#
# Index-based state_root extractor over witness.headers
# (SSZ list of parent header RLPs for BLOCKHASH).
#
# Output (40 bytes):
#   bytes  0.. 8 : status (0/1/2/3)
#   bytes  8..40 : state_root (32 B; zero on early-out)
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

echo "==> emit zisk_witness_headers_state_root_at_index ELF"
lake exe codegen --program zisk_witness_headers_state_root_at_index \
  --halt linux93 \
  -o gen-out/zisk_witness_headers_state_root_at_index

REPO_ROOT="$(pwd)"

run_case() {
  local name="$1"; shift
  local mode="$1"; shift
  local idx="$1"; shift

  local in_file="$REPO_ROOT/gen-out/zisk_whsr_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_whsr_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_whsr_${name}.expected"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys
import rlp

def encode_header(state_root_byte_fill):
    sr = bytes([state_root_byte_fill]) * 32
    fields = [
        b'\\x11'*32, b'\\x22'*32, b'\\x33'*20, sr, b'\\x55'*32,
        b'\\x66'*32, b'\\x00'*256, b'', b'\\x01', b'\\x83\\xff\\xff\\xff',
        b'', b'\\x83\\x01\\x02\\x03', b'', b'\\x77'*32, b'\\x00'*8,
    ]
    return rlp.encode(fields), sr

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

if mode == 'three_headers':
    hdrs = []
    srs = []
    for fill in (0x44, 0x55, 0x66):
        hdr, sr = encode_header(fill)
        hdrs.append(hdr)
        srs.append(sr)
    witness_headers = build_ssz_section(hdrs)
    if idx < len(hdrs):
        expected = struct.pack('<Q', 0) + srs[idx]
    else:
        expected = struct.pack('<Q', 1) + b'\\x00' * 32
elif mode == 'empty':
    witness_headers = b''
    expected = struct.pack('<Q', 1) + b'\\x00' * 32
elif mode == 'garbage_header_at_idx':
    # First entry valid, second entry garbage. Look up index 1.
    hdr0, sr0 = encode_header(0x44)
    bad = b'\\x00'  # too small to parse as RLP list of 15
    witness_headers = build_ssz_section([hdr0, bad])
    # idx=1 -> status 2 (parse fail, remapped from K201 status 1).
    expected = struct.pack('<Q', 2) + b'\\x00' * 32
else:
    raise SystemExit('bad mode')

with open(sys.argv[1], 'wb') as f:
    record = (
        struct.pack('<Q', len(witness_headers))
        + struct.pack('<Q', idx)
        + witness_headers
    )
    f.write(record)
    pad = (-len(record)) % 8
    if pad: f.write(b'\\x00' * pad)

with open(sys.argv[2], 'wb') as f:
    f.write(expected)
" "$in_file" "$exp_file"

  "$ZISKEMU" -e gen-out/zisk_witness_headers_state_root_at_index.elf \
    -i "$in_file" -o "$out_file" -n 4000000 \
    >"$REPO_ROOT/gen-out/zisk_whsr_${name}.emu.log" 2>&1 || true

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
# 1) Three valid headers, extract from each index.
run_case "three_idx0_first"              three_headers 0 || FAILED=1
run_case "three_idx1_middle"             three_headers 1 || FAILED=1
run_case "three_idx2_last"               three_headers 2 || FAILED=1
# 2) OOB index.
run_case "three_idx3_oob"                three_headers 3 || FAILED=1
# 3) Empty section.
run_case "empty_section_oob"             empty 0 || FAILED=1
# 4) Garbage header at index -> status 2.
run_case "garbage_header_at_idx1"        garbage_header_at_idx 1 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: witness_headers_state_root_at_index end-to-end"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
