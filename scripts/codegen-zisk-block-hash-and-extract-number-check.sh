#!/usr/bin/env bash
# codegen-zisk-block-hash-and-extract-number-check.sh -- PR-K213.
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

echo "==> emit zisk_block_hash_and_extract_number ELF"
lake exe codegen --program zisk_block_hash_and_extract_number --halt linux93 \
  -o gen-out/zisk_block_hash_and_extract_number

REPO_ROOT="$(pwd)"

run_case() {
  local name="$1" number="$2"

  local in_file="$REPO_ROOT/gen-out/zisk_block_hash_and_extract_number_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_block_hash_and_extract_number_${name}.output"
  local exp_hash_file="$REPO_ROOT/gen-out/zisk_block_hash_and_extract_number_${name}.expected.hex"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys, rlp
try:
    from Crypto.Hash import keccak
    def keccak256(b):
        h = keccak.new(digest_bits=256); h.update(b); return h.digest()
except Exception:
    import sha3
    def keccak256(b): return sha3.keccak_256(b).digest()

def u_be(n):
    if n == 0: return b''
    return n.to_bytes((n.bit_length() + 7) // 8, 'big')

num = $number
fields = [
    b'\\xa1'*32, b'\\xa2'*32, b'\\xa3'*20, b'\\xa4'*32, b'\\xa5'*32,
    b'\\xa6'*32, b'\\x00'*256, b'', u_be(num), b'\\x83\\xff\\xff\\xff',
    b'', b'\\x83\\x01\\x02\\x03', b'', b'\\xa7'*32, b'\\x00'*8,
]
header_rlp = rlp.encode(fields)
hash = keccak256(header_rlp)
with open(sys.argv[1], 'wb') as f:
    record = struct.pack('<Q', len(header_rlp)) + header_rlp
    f.write(record)
    pad = (-len(record)) % 8
    if pad: f.write(b'\x00' * pad)
with open(sys.argv[2], 'w') as f:
    f.write(hash.hex())
" "$in_file" "$exp_hash_file"

  "$ZISKEMU" -e gen-out/zisk_block_hash_and_extract_number.elf \
    -i "$in_file" -o "$out_file" -n 1000000 \
    >"$REPO_ROOT/gen-out/zisk_block_hash_and_extract_number_${name}.emu.log" 2>&1 || true

  local num_le; num_le="$(dd if="$out_file" bs=1 skip=8 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local actual_hash; actual_hash="$(dd if="$out_file" bs=1 skip=16 count=32 2>/dev/null | xxd -p | tr -d '\n')"
  local actual_num
  actual_num="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$num_le'))[0])")"
  local expected_hash="$(cat "$exp_hash_file")"

  if [[ "$actual_num" == "$number" && "$actual_hash" == "$expected_hash" ]]; then
    printf "  %-26s OK   num=%s hash=%s...\n" "$name" "$actual_num" "${actual_hash:0:16}"
    return 0
  else
    printf "  %-26s FAIL num=%s/%s hash=%s/%s\n" "$name" "$actual_num" "$number" "$actual_hash" "$expected_hash"
    return 1
  fi
}

FAILED=0
run_case "block_42"      42       || FAILED=1
run_case "block_zero"    0        || FAILED=1
run_case "block_big"     18000000 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: block_hash_and_extract_number returns (hash, number) pair"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
