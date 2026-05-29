#!/usr/bin/env bash
# codegen-zisk-witness-codes-validate-lengths-check.sh
#
# Walks the SSZ witness.codes list and verifies every entry's
# byte length is within a caller-supplied cap (typically the
# EIP-170 limit of 24576 bytes).
#
# Spec rationale: every entry in witness.codes is supposed to be
# deployed bytecode referenced by some account.code_hash. Per
# EIP-170, deployed code is capped at 24576 bytes. A witness
# whose codes section contains oversized blobs is malformed.
#
# Output (24 bytes):
#   bytes  0.. 8 : status (0 ok / 1 some entry too long)
#   bytes  8..16 : n_processed (= N on success; first bad index on fail)
#   bytes 16..24 : first_bad_index (0xFF..FF on success)
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

echo "==> emit zisk_witness_codes_validate_lengths ELF"
lake exe codegen --program zisk_witness_codes_validate_lengths \
  --halt linux93 \
  -o gen-out/zisk_witness_codes_validate_lengths

REPO_ROOT="$(pwd)"

# run_case <name> <mode> [args...]
#
#   empty <max_size>
#   uniform <count> <each_size> <max_size>
#   first_too_big <max_size>
#     One short entry then one over the cap.
#   exact_cap <max_size>
#     One entry of exactly max_size bytes (must pass).
run_case() {
  local name="$1"; shift
  local mode="$1"; shift

  local in_file="$REPO_ROOT/gen-out/zisk_wcvl_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_wcvl_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_wcvl_${name}.expected"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys

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

argv = sys.argv[1:]
mode = '$mode'
parts = [
$(for arg in "$@"; do printf '  %s,\n' "\"$arg\""; done)
]

MAX64 = (1 << 64) - 1

if mode == 'empty':
    max_size = int(parts[0])
    elements = []
    expected_status = 0
    expected_n = 0
    expected_bad = MAX64
elif mode == 'uniform':
    count = int(parts[0])
    each_size = int(parts[1])
    max_size = int(parts[2])
    elements = [bytes([i & 0xff]) * each_size for i in range(count)]
    if each_size > max_size:
        expected_status = 1
        expected_n = 0
        expected_bad = 0
    else:
        expected_status = 0
        expected_n = count
        expected_bad = MAX64
elif mode == 'first_too_big':
    max_size = int(parts[0])
    elements = [b'\\x60\\x00', b'\\xff' * (max_size + 1)]
    expected_status = 1
    expected_n = 1
    expected_bad = 1
elif mode == 'exact_cap':
    max_size = int(parts[0])
    elements = [b'\\xab' * max_size]
    expected_status = 0
    expected_n = 1
    expected_bad = MAX64
else:
    raise SystemExit('bad mode: ' + mode)

section = build_ssz_section(elements)
expected = (
    struct.pack('<Q', expected_status)
    + struct.pack('<Q', expected_n)
    + struct.pack('<Q', expected_bad)
)

with open(argv[0], 'wb') as f:
    record = struct.pack('<Q', len(section)) + struct.pack('<Q', max_size) + section
    f.write(record)
    pad = (-len(record)) % 8
    if pad: f.write(b'\\x00' * pad)

with open(argv[1], 'wb') as f:
    f.write(expected)
" "$in_file" "$exp_file"

  "$ZISKEMU" -e gen-out/zisk_witness_codes_validate_lengths.elf \
    -i "$in_file" -o "$out_file" -n 8000000 \
    >"$REPO_ROOT/gen-out/zisk_wcvl_${name}.emu.log" 2>&1 || true

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

# EIP-170 limit.
EIP170=24576

FAILED=0
run_case "empty_section"            empty $EIP170 || FAILED=1
run_case "single_short_code"        uniform 1 2 $EIP170 || FAILED=1
run_case "five_under_cap"           uniform 5 1000 $EIP170 || FAILED=1
# Spec-defining test: oversized entry detected.
run_case "first_too_big"            first_too_big $EIP170 || FAILED=1
# Boundary: exactly at the cap is OK.
run_case "exact_cap"                exact_cap $EIP170 || FAILED=1
# Oversized: all 5 entries over cap; first one (index 0) flagged.
run_case "all_over_cap"             uniform 5 100 50 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: witness_codes_validate_lengths end-to-end"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
