#!/usr/bin/env bash
# codegen-zisk-block-hash-matches-check.sh -- PR-K209.
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

echo "==> emit zisk_block_hash_matches ELF"
lake exe codegen --program zisk_block_hash_matches --halt linux93 \
  -o gen-out/zisk_block_hash_matches

REPO_ROOT="$(pwd)"

# run_case <name> <break_claim 0/1> <exp_valid>
run_case() {
  local name="$1" break_claim="$2" exp_valid="$3"

  local in_file="$REPO_ROOT/gen-out/zisk_block_hash_matches_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_block_hash_matches_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys, rlp
try:
    from Crypto.Hash import keccak
    def keccak256(b):
        h = keccak.new(digest_bits=256); h.update(b); return h.digest()
except Exception:
    import sha3
    def keccak256(b): return sha3.keccak_256(b).digest()

bad = $break_claim == 1

fields = [
    b'\\x11'*32, b'\\x22'*32, b'\\x33'*20, b'\\x44'*32, b'\\x55'*32,
    b'\\x66'*32, b'\\x00'*256, b'', b'\\x01', b'\\x83\\xff\\xff\\xff',
    b'', b'\\x83\\x01\\x02\\x03', b'', b'\\x77'*32, b'\\x00'*8,
]
header_rlp = rlp.encode(fields)
real = keccak256(header_rlp)
claimed = bytes([b ^ 0xff for b in real]) if bad else real

with open(sys.argv[1], 'wb') as f:
    record = struct.pack('<Q', len(header_rlp)) + claimed + header_rlp
    f.write(record)
    pad = (-len(record)) % 8
    if pad: f.write(b'\x00' * pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_block_hash_matches.elf \
    -i "$in_file" -o "$out_file" -n 1000000 \
    >"$REPO_ROOT/gen-out/zisk_block_hash_matches_${name}.emu.log" 2>&1 || true

  local status_le; status_le="$(xxd -p -l 8 "$out_file" | tr -d '\n')"
  local valid_le;  valid_le="$( dd if="$out_file" bs=1 skip=8 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local valid
  valid="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$valid_le'))[0])")"

  if [[ "$valid" == "$exp_valid" ]]; then
    printf "  %-26s OK   valid=%s\n" "$name" "$valid"
    return 0
  else
    printf "  %-26s FAIL valid=%s/%s\n" "$name" "$valid" "$exp_valid"
    return 1
  fi
}

FAILED=0
run_case "match"      0 1 || FAILED=1
run_case "mismatch"   1 0 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: block_hash_matches verifies keccak256(header) == claim"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
