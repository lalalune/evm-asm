#!/usr/bin/env bash
# codegen-zisk-witness-headers-chain-validate-check.sh
#
# Verify that an SSZ witness.headers list is a coherent chain:
# for each consecutive pair (headers[i], headers[i+1]),
#   keccak256(headers[i]) == headers[i+1].parent_hash.
#
# Walks the SSZ list with the same per-element iteration pattern
# as PR #7147 blockhash_from_witness_headers.
#
# Output (24 bytes):
#   bytes  0.. 8 : status (0 ok / 1 mismatch / 2 RLP parse fail)
#   bytes  8..16 : n_pairs_checked (or first failing parent index)
#   bytes 16..24 : first_mismatch_index (0xFF..FF on success)
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

echo "==> emit zisk_witness_headers_chain_validate ELF"
lake exe codegen --program zisk_witness_headers_chain_validate \
  --halt linux93 \
  -o gen-out/zisk_witness_headers_chain_validate

REPO_ROOT="$(pwd)"

# run_case <name> <mode> [args...]
#
#   coherent <N>
#     Build N headers chained correctly: header[i+1].parent_hash = keccak(header[i]).
#     Expect (status=0, n_pairs=N-1, mismatch_idx=0xFF..FF).
#
#   break_at <N> <break_idx>
#     Build N headers, but break header[break_idx+1].parent_hash to garbage.
#     Expect (status=1, n_pairs=break_idx, mismatch_idx=break_idx).
#
#   parse_fail <N>
#     Replace one header in the section with 1-byte garbage that fails
#     parent_hash extraction. Expect status=2.
#
#   empty
#     Empty witness.headers; expect (0, 0, 0xFF..FF).
#
#   singleton
#     One header; expect (0, 0, 0xFF..FF) - vacuously valid.
run_case() {
  local name="$1"; shift
  local mode="$1"; shift

  local in_file="$REPO_ROOT/gen-out/zisk_wchv_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_wchv_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_wchv_${name}.expected"

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

def header_with_parent_and_number(parent_hash, n):
    nb = n.to_bytes((n.bit_length() + 7) // 8, 'big') if n > 0 else b''
    fields = [
        parent_hash, b'\\x22'*32, b'\\x33'*20, b'\\x44'*32, b'\\x55'*32,
        b'\\x66'*32, b'\\x00'*256, b'',
        nb,
        b'\\x83\\xff\\xff\\xff', b'', b'\\x83\\x01\\x02\\x03', b'',
        b'\\x77'*32, b'\\x00'*8,
    ]
    return rlp.encode(fields)

def build_coherent_chain(N, start_parent=b'\\x00'*32, start_n=100):
    headers = []
    prev_hash = start_parent
    for i in range(N):
        h = header_with_parent_and_number(prev_hash, start_n + i)
        headers.append(h)
        prev_hash = k256(h)
    return headers

argv = sys.argv[1:]
mode = '$mode'
parts = [
$(for arg in "$@"; do printf '  %s,\n' "\"$arg\""; done)
]

MAX64 = (1 << 64) - 1

if mode == 'coherent':
    N = int(parts[0])
    headers = build_coherent_chain(N)
    section = build_ssz_section(headers)
    expected = (
        struct.pack('<Q', 0)
        + struct.pack('<Q', max(N - 1, 0))
        + struct.pack('<Q', MAX64)
    )
elif mode == 'break_at':
    N = int(parts[0])
    break_idx = int(parts[1])
    headers = build_coherent_chain(N)
    # Replace headers[break_idx + 1] with one that has a wrong parent_hash.
    wrong_parent = b'\\xff' * 32
    headers[break_idx + 1] = header_with_parent_and_number(wrong_parent, 200 + break_idx)
    # Adjust subsequent headers to chain off the rebuilt one so only
    # the (break_idx, break_idx+1) pair is broken.
    prev = k256(headers[break_idx + 1])
    for j in range(break_idx + 2, N):
        headers[j] = header_with_parent_and_number(prev, 200 + j)
        prev = k256(headers[j])
    section = build_ssz_section(headers)
    expected = (
        struct.pack('<Q', 1)
        + struct.pack('<Q', break_idx)
        + struct.pack('<Q', break_idx)
    )
elif mode == 'parse_fail':
    N = int(parts[0])
    headers = build_coherent_chain(N)
    # Replace one header (index 1, the child of the first pair) with garbage.
    headers[1] = b'\\x00'
    section = build_ssz_section(headers)
    # The first pair will fail to extract parent_hash from the garbage child.
    expected = (
        struct.pack('<Q', 2)
        + struct.pack('<Q', 0)
        + struct.pack('<Q', 0)
    )
elif mode == 'empty':
    section = b''
    expected = (
        struct.pack('<Q', 0)
        + struct.pack('<Q', 0)
        + struct.pack('<Q', MAX64)
    )
elif mode == 'singleton':
    headers = build_coherent_chain(1)
    section = build_ssz_section(headers)
    expected = (
        struct.pack('<Q', 0)
        + struct.pack('<Q', 0)
        + struct.pack('<Q', MAX64)
    )
else:
    raise SystemExit('bad mode: ' + mode)

with open(argv[0], 'wb') as f:
    record = struct.pack('<Q', len(section)) + section
    f.write(record)
    pad = (-len(record)) % 8
    if pad: f.write(b'\\x00' * pad)

with open(argv[1], 'wb') as f:
    f.write(expected)
" "$in_file" "$exp_file"

  "$ZISKEMU" -e gen-out/zisk_witness_headers_chain_validate.elf \
    -i "$in_file" -o "$out_file" -n 8000000 \
    >"$REPO_ROOT/gen-out/zisk_wchv_${name}.emu.log" 2>&1 || true

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
run_case "empty"                empty || FAILED=1
run_case "singleton"            singleton || FAILED=1
run_case "coherent_2"           coherent 2 || FAILED=1
run_case "coherent_5"           coherent 5 || FAILED=1
run_case "break_first_pair"     break_at 4 0 || FAILED=1
run_case "break_middle_pair"    break_at 5 2 || FAILED=1
run_case "break_last_pair"      break_at 5 3 || FAILED=1
run_case "parse_fail_garbage"   parse_fail 3 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: witness_headers_chain_validate end-to-end"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
