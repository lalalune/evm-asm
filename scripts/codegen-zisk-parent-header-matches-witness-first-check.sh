#!/usr/bin/env bash
# codegen-zisk-parent-header-matches-witness-first-check.sh
#
# Cross-input consistency check: parent_header_rlp matches
# witness.headers[0] byte-for-byte.
#
# Output (16 bytes):
#   bytes  0.. 8 : status (0 / 1)
#   bytes  8..16 : is_match (u64; 0 or 1)
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

echo "==> emit zisk_parent_header_matches_witness_first ELF"
lake exe codegen --program zisk_parent_header_matches_witness_first \
  --halt linux93 \
  -o gen-out/zisk_parent_header_matches_witness_first

REPO_ROOT="$(pwd)"

# run_case <name> <mode> <numbers_csv> <provided_idx>
#   match_at_0: witness has headers with numbers from CSV, parent header is the first one.
#   mismatch:   witness has headers, parent header is a different one (e.g., the second).
#   different_length: parent header has a different length from witness[0].
#   empty: empty witness.headers section.
run_case() {
  local name="$1"; shift
  local mode="$1"; shift

  local in_file="$REPO_ROOT/gen-out/zisk_phmw_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_phmw_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_phmw_${name}.expected"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys
import rlp

def build_ssz_section(elements):
    n = len(elements)
    if n == 0:
        return b''
    section = b''
    offset = 4 * n
    for e in elements:
        section += struct.pack('<I', offset)
        offset += len(e)
    for e in elements:
        section += e
    return section

def header_with_number(n):
    nb = n.to_bytes((n.bit_length() + 7) // 8, 'big') if n > 0 else b''
    fields = [
        b'\\x11'*32, b'\\x22'*32, b'\\x33'*20, b'\\x44'*32, b'\\x55'*32,
        b'\\x66'*32, b'\\x00'*256, b'', nb, b'\\x83\\xff\\xff\\xff',
        b'', b'\\x83\\x01\\x02\\x03', b'', b'\\x77'*32, b'\\x00'*8,
    ]
    return rlp.encode(fields)

argv = sys.argv[1:]
mode = '$mode'
parts = [
$(for arg in "$@"; do printf '  %s,\n' "\"$arg\""; done)
]

if mode == 'match_at_0':
    numbers = [int(p) for p in parts[0].split(',') if p]
    headers = [header_with_number(n) for n in numbers]
    section = build_ssz_section(headers)
    parent_header = headers[0]
    expected_status = 0
    expected_is_match = 1
elif mode == 'mismatch':
    numbers = [int(p) for p in parts[0].split(',') if p]
    headers = [header_with_number(n) for n in numbers]
    section = build_ssz_section(headers)
    # Use the SECOND header as parent (same length, different content).
    parent_header = headers[1]
    expected_status = 0
    expected_is_match = 0
elif mode == 'different_length':
    # Witness has a normal header at index 0; parent_header is 1 byte garbage.
    headers = [header_with_number(100), header_with_number(99)]
    section = build_ssz_section(headers)
    parent_header = b'\\x00'  # 1 byte; length mismatch with witness[0]
    expected_status = 0
    expected_is_match = 0
elif mode == 'empty':
    section = b''
    parent_header = header_with_number(100)
    expected_status = 1
    expected_is_match = 0
else:
    raise SystemExit('bad mode: ' + mode)

expected = struct.pack('<Q', expected_status) + struct.pack('<Q', expected_is_match)

with open(argv[0], 'wb') as f:
    record = (
        struct.pack('<Q', len(parent_header))
        + struct.pack('<Q', len(section))
        + parent_header
        + section
    )
    f.write(record)
    pad = (-len(record)) % 8
    if pad: f.write(b'\\x00' * pad)

with open(argv[1], 'wb') as f:
    f.write(expected)
" "$in_file" "$exp_file"

  "$ZISKEMU" -e gen-out/zisk_parent_header_matches_witness_first.elf \
    -i "$in_file" -o "$out_file" -n 4000000 \
    >"$REPO_ROOT/gen-out/zisk_phmw_${name}.emu.log" 2>&1 || true

  local exp_size; exp_size="$(stat -c%s "$exp_file")"
  local actual expected
  actual="$(xxd -p -l "$exp_size" "$out_file" 2>/dev/null | tr -d '\n')"
  expected="$(xxd -p -l "$exp_size" "$exp_file" 2>/dev/null | tr -d '\n')"

  if [[ "$actual" == "$expected" ]]; then
    printf "  %-30s OK   %d bytes match\n" "$name" "$exp_size"
    return 0
  else
    printf "  %-30s FAIL\n    expected: %s\n    actual:   %s\n" \
      "$name" "$expected" "$actual"
    return 1
  fi
}

FAILED=0
run_case "match_single_header"   match_at_0 "100" || FAILED=1
run_case "match_first_of_three"  match_at_0 "100,200,300" || FAILED=1
run_case "mismatch_diff_header"  mismatch "100,200" || FAILED=1
run_case "mismatch_diff_length"  different_length || FAILED=1
run_case "empty_section"         empty || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: parent_header_matches_witness_first end-to-end"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
