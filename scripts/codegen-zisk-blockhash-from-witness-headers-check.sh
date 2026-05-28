#!/usr/bin/env bash
# codegen-zisk-blockhash-from-witness-headers-check.sh
#
# BLOCKHASH-opcode semantics over a stateless witness: given a
# target block number, find the matching header in
# witness.headers and return keccak256(header_rlp).
#
# Composes K233 header_extract_number + zkvm_keccak256 over the
# witness.headers SSZ list layout.
#
# Output (40 bytes):
#   bytes  0.. 8 : status (0 hit / 1 miss / 2 parse_fail)
#   bytes  8..16 : matched offset within section (on hit)
#   bytes 16..24 : matched length within section (on hit)
#   bytes 24..56 : block hash (on hit; zeros otherwise)
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

echo "==> emit zisk_blockhash_from_witness_headers ELF"
lake exe codegen --program zisk_blockhash_from_witness_headers \
  --halt linux93 \
  -o gen-out/zisk_blockhash_from_witness_headers

REPO_ROOT="$(pwd)"

# run_case <name> <mode> [args...]
#
#   hit <target_n> <numbers_csv>
#     witness.headers = N synthetic headers with numbers from
#     numbers_csv; lookup target_n which must be in numbers_csv.
#     Expected: status 0, matched offset/length, keccak.
#
#   miss <target_n> <numbers_csv>
#     Same but target_n is NOT in numbers_csv.
#     Expected: status 1, zeros.
#
#   parse_fail <target_n>
#     witness.headers contains one 1-byte garbage entry; should
#     surface as status 2.
run_case() {
  local name="$1"; shift
  local mode="$1"; shift

  local in_file="$REPO_ROOT/gen-out/zisk_bhfwh_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_bhfwh_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_bhfwh_${name}.expected"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys
import rlp
from Crypto.Hash import keccak

def k256(b):
    h = keccak.new(digest_bits=256); h.update(b); return h.digest()

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
    number_bytes = n.to_bytes((n.bit_length() + 7) // 8, 'big') if n > 0 else b''
    fields = [
        b'\\x11'*32, b'\\x22'*32, b'\\x33'*20, b'\\x44'*32, b'\\x55'*32,
        b'\\x66'*32, b'\\x00'*256, b'',
        number_bytes,
        b'\\x83\\xff\\xff\\xff', b'',
        b'\\x83\\x01\\x02\\x03', b'', b'\\x77'*32, b'\\x00'*8,
    ]
    return rlp.encode(fields)

argv = sys.argv[1:]
mode = '$mode'
parts = [
$(for arg in "$@"; do printf '  %s,\n' "\"$arg\""; done)
]

if mode == 'hit':
    target = int(parts[0])
    numbers = [int(p) for p in parts[1].split(',') if p]
    headers = [header_with_number(n) for n in numbers]
    section = build_ssz_section(headers)
    # Find matched index
    idx = numbers.index(target)
    # Compute offset/length within the section.
    N = len(headers)
    offset = 4 * N
    for i in range(idx):
        offset += len(headers[i])
    length = len(headers[idx])
    block_hash = k256(headers[idx])
    expected = (
        struct.pack('<Q', 0)
        + struct.pack('<Q', offset)
        + struct.pack('<Q', length)
        + block_hash
    )
elif mode == 'miss':
    target = int(parts[0])
    numbers = [int(p) for p in parts[1].split(',') if p]
    headers = [header_with_number(n) for n in numbers]
    section = build_ssz_section(headers)
    expected = struct.pack('<Q', 1) + b'\\x00' * 48
elif mode == 'parse_fail':
    target = int(parts[0])
    headers = [b'\\xc0']  # RLP empty list -- has no field-8 number
    section = build_ssz_section(headers)
    expected = struct.pack('<Q', 2) + b'\\x00' * 48
else:
    raise SystemExit('bad mode: ' + mode)

with open(argv[0], 'wb') as f:
    record = (
        struct.pack('<Q', target)
        + struct.pack('<Q', len(section))
        + section
    )
    f.write(record)
    pad = (-len(record)) % 8
    if pad: f.write(b'\\x00' * pad)

with open(argv[1], 'wb') as f:
    f.write(expected)
" "$in_file" "$exp_file"

  "$ZISKEMU" -e gen-out/zisk_blockhash_from_witness_headers.elf \
    -i "$in_file" -o "$out_file" -n 4000000 \
    >"$REPO_ROOT/gen-out/zisk_bhfwh_${name}.emu.log" 2>&1 || true

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
run_case "hit_single"              hit 100 "100" || FAILED=1
run_case "hit_first_of_three"      hit 100 "100,200,300" || FAILED=1
run_case "hit_middle_of_three"     hit 200 "100,200,300" || FAILED=1
run_case "hit_last_of_three"       hit 300 "100,200,300" || FAILED=1
run_case "miss_smaller"            miss 50 "100,200,300" || FAILED=1
run_case "miss_larger"             miss 999 "100,200,300" || FAILED=1
run_case "miss_empty_section"      miss 100 "" || FAILED=1
run_case "parse_fail"              parse_fail 100 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: blockhash_from_witness_headers end-to-end"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
