#!/usr/bin/env bash
# codegen-zisk-mpt-encode-internal-node-check.sh -- PR-K112.
#
# MPT node reference: keccak256 if >=32 bytes, else embed bytes.
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

echo "==> emit zisk_mpt_encode_internal_node ELF"
lake exe codegen --program zisk_mpt_encode_internal_node --halt linux93 \
  -o gen-out/zisk_mpt_encode_internal_node

REPO_ROOT="$(pwd)"

# run_case <name> <bytes_hex>
run_case() {
  local name="$1" bytes_hex="$2"

  local in_file="$REPO_ROOT/gen-out/zisk_mpt_encode_internal_node_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_mpt_encode_internal_node_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys
from Crypto.Hash import keccak
b = bytes.fromhex('$bytes_hex')
with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(b)))
    f.write(b)
    pad = (-(8 + len(b))) % 8
    if pad: f.write(b'\x00' * pad)
if len(b) < 32:
    expected_bytes = b
    expected_len = len(b)
    is_hashed = 0
else:
    expected_bytes = keccak.new(digest_bits=256).update(b).digest()
    expected_len = 32
    is_hashed = 1
with open(sys.argv[1] + '.expected', 'wb') as f:
    f.write(struct.pack('<Q', expected_len))
    f.write(struct.pack('<Q', is_hashed))
    f.write(expected_bytes)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_mpt_encode_internal_node.elf \
    -i "$in_file" -o "$out_file" -n 5000000 \
    >"$REPO_ROOT/gen-out/zisk_mpt_encode_internal_node_${name}.emu.log" 2>&1 || true

  local actual_status; actual_status="$(xxd -p -l 8 "$out_file" | tr -d '\n')"
  local actual_len_le; actual_len_le="$(dd if="$out_file" bs=1 skip=8 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local actual_len; actual_len="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$actual_len_le'))[0])")"
  local actual_hashed_le; actual_hashed_le="$(dd if="$out_file" bs=1 skip=16 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local actual_hashed; actual_hashed="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$actual_hashed_le'))[0])")"

  local expected_len_le; expected_len_le="$(dd if="$in_file.expected" bs=1 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local expected_len; expected_len="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$expected_len_le'))[0])")"
  local expected_hashed_le; expected_hashed_le="$(dd if="$in_file.expected" bs=1 skip=8 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local expected_hashed; expected_hashed="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$expected_hashed_le'))[0])")"

  if [[ "$actual_status" != "0000000000000000" ]]; then
    printf "  %-32s FAIL status=0x%s\n" "$name" "$actual_status"
    return 1
  fi
  if [[ "$actual_len" != "$expected_len" || "$actual_hashed" != "$expected_hashed" ]]; then
    printf "  %-32s FAIL len=%d expected=%d hashed=%d expected=%d\n" "$name" "$actual_len" "$expected_len" "$actual_hashed" "$expected_hashed"
    return 1
  fi
  local actual_bytes; actual_bytes="$(dd if="$out_file" bs=1 skip=24 count="$expected_len" 2>/dev/null | xxd -p | tr -d '\n')"
  local expected_bytes; expected_bytes="$(dd if="$in_file.expected" bs=1 skip=16 count="$expected_len" 2>/dev/null | xxd -p | tr -d '\n')"
  if [[ "$actual_bytes" == "$expected_bytes" ]]; then
    printf "  %-32s OK   len=%d hashed=%d\n" "$name" "$expected_len" "$expected_hashed"
    return 0
  else
    printf "  %-32s FAIL bytes mismatch\n    expected: %s\n    actual:   %s\n" "$name" "${expected_bytes:0:40}" "${actual_bytes:0:40}"
    return 1
  fi
}

FAILED=0
# Embedded cases (< 32 bytes)
run_case "embed_1byte"        "ab" || FAILED=1
run_case "embed_31bytes"      "$(python3 -c "print('aa' * 31)")" || FAILED=1
run_case "embed_small_list"   "c102" || FAILED=1
# Boundary
run_case "hash_32bytes"       "$(python3 -c "print('aa' * 32)")" || FAILED=1
# Hashed cases (>= 32 bytes)
run_case "hash_64bytes"       "$(python3 -c "print('cc' * 64)")" || FAILED=1
run_case "hash_typical_leaf"  "$(python3 -c "print('e2' + 'd0' + 'aa' * 32 + 'cc' * 4)")" || FAILED=1
run_case "hash_long"          "$(python3 -c "print('ab' * 200)")" || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: mpt_encode_internal_node returns embed-or-hash per encode_internal_node"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
