#!/usr/bin/env bash
# codegen-zisk-block-validate-block-hash-pair-check.sh -- PR-K212.
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

echo "==> emit zisk_block_validate_block_hash_pair ELF"
lake exe codegen --program zisk_block_validate_block_hash_pair --halt linux93 \
  -o gen-out/zisk_block_validate_block_hash_pair

REPO_ROOT="$(pwd)"

run_case() {
  local name="$1" break_link="$2" exp_valid="$3"

  local in_file="$REPO_ROOT/gen-out/zisk_block_validate_block_hash_pair_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_block_validate_block_hash_pair_${name}.output"
  local exp_hashes_file="$REPO_ROOT/gen-out/zisk_block_validate_block_hash_pair_${name}.expected.hex"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys, rlp
try:
    from Crypto.Hash import keccak
    def keccak256(b):
        h = keccak.new(digest_bits=256); h.update(b); return h.digest()
except Exception:
    import sha3
    def keccak256(b): return sha3.keccak_256(b).digest()

bad = $break_link == 1

parent_fields = [
    b'\\xa1'*32, b'\\xa2'*32, b'\\xa3'*20, b'\\xa4'*32, b'\\xa5'*32,
    b'\\xa6'*32, b'\\x00'*256, b'', b'\\x01', b'\\x83\\xff\\xff\\xff',
    b'', b'\\x83\\x01\\x02\\x03', b'', b'\\xa7'*32, b'\\x00'*8,
]
parent_rlp = rlp.encode(parent_fields)
parent_hash = keccak256(parent_rlp)

claimed = bytes([b ^ 0xff for b in parent_hash]) if bad else parent_hash

child_fields = [
    claimed, b'\\xb2'*32, b'\\xb3'*20, b'\\xb4'*32, b'\\xb5'*32,
    b'\\xb6'*32, b'\\x00'*256, b'', b'\\x02', b'\\x83\\xff\\xff\\xff',
    b'', b'\\x83\\x01\\x02\\x04', b'', b'\\xb7'*32, b'\\x00'*8,
]
child_rlp = rlp.encode(child_fields)
child_hash = keccak256(child_rlp)

with open(sys.argv[1], 'wb') as f:
    record = struct.pack('<Q', len(parent_rlp)) + \
             struct.pack('<Q', len(child_rlp)) + \
             parent_rlp + child_rlp
    f.write(record)
    pad = (-len(record)) % 8
    if pad: f.write(b'\x00' * pad)
with open(sys.argv[2], 'w') as f:
    f.write(parent_hash.hex() + ',' + child_hash.hex())
" "$in_file" "$exp_hashes_file"

  "$ZISKEMU" -e gen-out/zisk_block_validate_block_hash_pair.elf \
    -i "$in_file" -o "$out_file" -n 2000000 \
    >"$REPO_ROOT/gen-out/zisk_block_validate_block_hash_pair_${name}.emu.log" 2>&1 || true

  local valid_le; valid_le="$(dd if="$out_file" bs=1 skip=8 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local parent_hash; parent_hash="$(dd if="$out_file" bs=1 skip=16 count=32 2>/dev/null | xxd -p | tr -d '\n')"
  local child_hash;  child_hash="$( dd if="$out_file" bs=1 skip=48 count=32 2>/dev/null | xxd -p | tr -d '\n')"
  local valid
  valid="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$valid_le'))[0])")"
  local exp_parent="$(cut -d, -f1 "$exp_hashes_file")"
  local exp_child="$(cut -d, -f2 "$exp_hashes_file")"

  if [[ "$valid" == "$exp_valid" && "$parent_hash" == "$exp_parent" && "$child_hash" == "$exp_child" ]]; then
    printf "  %-26s OK   valid=%s parent=%s... child=%s...\n" "$name" "$valid" "${parent_hash:0:16}" "${child_hash:0:16}"
    return 0
  else
    printf "  %-26s FAIL valid=%s/%s phash=%s/exp%s chash=%s/exp%s\n" \
      "$name" "$valid" "$exp_valid" "$parent_hash" "$exp_parent" "$child_hash" "$exp_child"
    return 1
  fi
}

FAILED=0
run_case "matching_link" 0 1 || FAILED=1
run_case "broken_link"   1 0 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: block_validate_block_hash_pair outputs both hashes + validity"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
