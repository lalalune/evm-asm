#!/usr/bin/env bash
# codegen-zisk-blockhash-opcode-windowed-check.sh
#
# Full EVM BLOCKHASH(n) opcode semantic with the spec-mandated
# 256-block window check. Distinct from PR #7147
# (blockhash_from_witness_headers, raw lookup): this primitive
# returns 0 for out-of-window queries (BLOCKHASH(self),
# BLOCKHASH(future), or beyond the 256-block window) EVEN WHEN
# the witness happens to contain that header.
#
# Output (40 bytes):
#   bytes  0.. 8 : status (0 / 4 / 5)
#   bytes  8..40 : block hash (32 bytes; zeros for out-of-window
#                  or window-OK miss / error)
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

echo "==> emit zisk_blockhash_opcode_windowed ELF"
lake exe codegen --program zisk_blockhash_opcode_windowed \
  --halt linux93 \
  -o gen-out/zisk_blockhash_opcode_windowed

REPO_ROOT="$(pwd)"

# run_case <name> <mode> [args...]
#
#   in_window  <cur_num> <target_num> <numbers_csv>
#     witness.headers numbers come from numbers_csv (one per
#     header). Expect hit if target in [cur-256, cur-1].
#
#   out_of_window  <cur_num> <target_num> <numbers_csv>
#     target outside [cur-256, cur-1] but witness has target.
#     Expect zeros (status 0).
#
#   in_window_miss  <cur_num> <target_num> <numbers_csv>
#     target in window, but witness doesn't include it.
#     Expect status 5.
#
#   garbage_current_header <target_num>
#     1-byte garbage current header. Expect status 4.
run_case() {
  local name="$1"; shift
  local mode="$1"; shift

  local in_file="$REPO_ROOT/gen-out/zisk_bhow_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_bhow_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_bhow_${name}.expected"

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

if mode == 'in_window':
    cur_num = int(parts[0])
    target_num = int(parts[1])
    numbers = [int(p) for p in parts[2].split(',') if p]
    headers = [header_with_number(n) for n in numbers]
    section = build_ssz_section(headers)
    cur_header = header_with_number(cur_num)
    # target must be in [cur-256, cur-1] AND in numbers
    idx = numbers.index(target_num)
    target_header = headers[idx]
    target_hash = k256(target_header)
    expected_status = 0
    expected_hash = target_hash
elif mode == 'out_of_window':
    cur_num = int(parts[0])
    target_num = int(parts[1])
    numbers = [int(p) for p in parts[2].split(',') if p]
    headers = [header_with_number(n) for n in numbers]
    section = build_ssz_section(headers)
    cur_header = header_with_number(cur_num)
    # Even though witness has target, opcode returns 0.
    expected_status = 0
    expected_hash = b'\\x00' * 32
elif mode == 'in_window_miss':
    cur_num = int(parts[0])
    target_num = int(parts[1])
    numbers = [int(p) for p in parts[2].split(',') if p]
    headers = [header_with_number(n) for n in numbers]
    section = build_ssz_section(headers)
    cur_header = header_with_number(cur_num)
    # target in window but absent from witness -> integrity violation (5).
    expected_status = 5
    expected_hash = b'\\x00' * 32
elif mode == 'garbage_current_header':
    target_num = int(parts[0])
    cur_header = b'\\x00'
    section = b''
    expected_status = 4
    expected_hash = b'\\x00' * 32
else:
    raise SystemExit('bad mode: ' + mode)

expected = struct.pack('<Q', expected_status) + expected_hash

with open(argv[0], 'wb') as f:
    record = (
        struct.pack('<Q', len(cur_header))
        + struct.pack('<Q', len(section))
        + struct.pack('<Q', target_num)
        + cur_header
        + section
    )
    f.write(record)
    pad = (-len(record)) % 8
    if pad: f.write(b'\\x00' * pad)

with open(argv[1], 'wb') as f:
    f.write(expected)
" "$in_file" "$exp_file"

  "$ZISKEMU" -e gen-out/zisk_blockhash_opcode_windowed.elf \
    -i "$in_file" -o "$out_file" -n 4000000 \
    >"$REPO_ROOT/gen-out/zisk_bhow_${name}.emu.log" 2>&1 || true

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
# Normal lookups, in-window.
run_case "in_window_basic"          in_window 500 499 "499,498,497" || FAILED=1
run_case "in_window_edge_minus1"    in_window 500 499 "499" || FAILED=1
run_case "in_window_edge_minus256"  in_window 500 244 "499,400,244" || FAILED=1
# Spec-defining tests: out-of-window returns 0 EVEN IF witness has it.
run_case "blockhash_self"           out_of_window 500 500 "500,499,498" || FAILED=1
run_case "blockhash_future"         out_of_window 500 600 "499,498,600" || FAILED=1
run_case "edge_minus257"            out_of_window 500 243 "499,243,400" || FAILED=1
# In-window but witness doesn't have it.
run_case "in_window_missing"        in_window_miss 500 400 "499,300" || FAILED=1
# Garbage current header.
run_case "garbage_current_header"   garbage_current_header 100 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: blockhash_opcode_windowed end-to-end"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
