#!/usr/bin/env bash
# codegen-zisk-witness-headers-max-block-number-check.sh
#
# Walk witness.headers and compute max(headers[i].number).
# Sibling of PR #7180 (min). Tells stateless guests the
# BLOCKHASH window's upper bound (typically parent.number).
#
# Output (24 bytes):
#   bytes  0.. 8 : status (0 ok / 2 parse fail)
#   bytes  8..16 : max_block_number (0 on empty section)
#   bytes 16..24 : n_processed (= N on success; failing index on fail)
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

echo "==> emit zisk_witness_headers_max_block_number ELF"
lake exe codegen --program zisk_witness_headers_max_block_number \
  --halt linux93 \
  -o gen-out/zisk_witness_headers_max_block_number

REPO_ROOT="$(pwd)"

run_case() {
  local name="$1"; shift
  local mode="$1"; shift

  local in_file="$REPO_ROOT/gen-out/zisk_whmax_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_whmax_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_whmax_${name}.expected"

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

if mode == 'empty':
    elements = []
    expected_status = 0
    expected_max = 0
    expected_n = 0
elif mode == 'one':
    n = int(parts[0])
    elements = [header_with_number(n)]
    expected_status = 0
    expected_max = n
    expected_n = 1
elif mode == 'monotonic':
    numbers = [int(p) for p in parts[0].split(',') if p]
    elements = [header_with_number(n) for n in numbers]
    expected_status = 0
    expected_max = max(numbers)
    expected_n = len(numbers)
elif mode == 'parse_fail_at':
    bad_idx = int(parts[0])
    elements = [header_with_number(100 + i) for i in range(bad_idx + 2)]
    elements[bad_idx] = b'\\x00'
    expected_status = 2
    # On parse-fail the max output remains at the pre-fill 0 (no commit on fail).
    expected_max = 0
    expected_n = bad_idx
else:
    raise SystemExit('bad mode: ' + mode)

section = build_ssz_section(elements)
expected = (
    struct.pack('<Q', expected_status)
    + struct.pack('<Q', expected_max)
    + struct.pack('<Q', expected_n)
)

with open(argv[0], 'wb') as f:
    record = struct.pack('<Q', len(section)) + section
    f.write(record)
    pad = (-len(record)) % 8
    if pad: f.write(b'\\x00' * pad)

with open(argv[1], 'wb') as f:
    f.write(expected)
" "$in_file" "$exp_file"

  "$ZISKEMU" -e gen-out/zisk_witness_headers_max_block_number.elf \
    -i "$in_file" -o "$out_file" -n 4000000 \
    >"$REPO_ROOT/gen-out/zisk_whmax_${name}.emu.log" 2>&1 || true

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
run_case "empty_section"        empty || FAILED=1
run_case "one_header_100"       one 100 || FAILED=1
run_case "one_genesis"          one 0 || FAILED=1
run_case "descending"           monotonic "300,200,100" || FAILED=1
run_case "ascending"            monotonic "100,200,300" || FAILED=1
run_case "max_in_middle"        monotonic "50,200,150" || FAILED=1
run_case "parse_fail_first"     parse_fail_at 0 || FAILED=1
run_case "parse_fail_third"     parse_fail_at 2 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: witness_headers_max_block_number end-to-end"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
