#!/usr/bin/env bash
# codegen-zisk-chain-block-hashes-commitment-check.sh -- PR-K200.
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

echo "==> emit zisk_chain_block_hashes_commitment ELF"
lake exe codegen --program zisk_chain_block_hashes_commitment --halt linux93 \
  -o gen-out/zisk_chain_block_hashes_commitment

REPO_ROOT="$(pwd)"

# run_case <name> <numbers_list_py>
run_case() {
  local name="$1" nums="$2"

  local in_file="$REPO_ROOT/gen-out/zisk_chain_block_hashes_commitment_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_chain_block_hashes_commitment_${name}.output"
  local exp_hex_file="$REPO_ROOT/gen-out/zisk_chain_block_hashes_commitment_${name}.expected.hex"

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

def make_header(num):
    return rlp.encode([
        b'\\xa1'*32, b'\\xa2'*32, b'\\xa3'*20, b'\\xa4'*32, b'\\xa5'*32,
        b'\\xa6'*32, b'\\x00'*256, b'', u_be(num), b'\\x83\\xff\\xff\\xff',
        b'\\x82\\x02\\x00', b'\\x83\\x01\\x02\\x03', b'', b'\\xa7'*32, b'\\x00'*8,
    ])

nums = $nums
headers = [make_header(n) for n in nums]
hashes = [keccak256(h) for h in headers]
commit = keccak256(b''.join(hashes))

N = len(headers)
lengths = b''.join(struct.pack('<Q', len(h)) for h in headers)
flat = b''.join(headers)

with open(sys.argv[1], 'wb') as f:
    record = struct.pack('<Q', N) + lengths + flat
    f.write(record)
    pad = (-len(record)) % 8
    if pad: f.write(b'\x00' * pad)
with open(sys.argv[2], 'w') as f:
    f.write(commit.hex())
" "$in_file" "$exp_hex_file"

  "$ZISKEMU" -e gen-out/zisk_chain_block_hashes_commitment.elf \
    -i "$in_file" -o "$out_file" -n 20000000 \
    >"$REPO_ROOT/gen-out/zisk_chain_block_hashes_commitment_${name}.emu.log" 2>&1 || true

  local actual; actual="$(xxd -p -l 32 "$out_file" | tr -d '\n')"
  local expected; expected="$(cat "$exp_hex_file")"

  if [[ "$actual" == "$expected" ]]; then
    printf "  %-26s OK   commit=%s...\n" "$name" "${actual:0:16}"
    return 0
  else
    printf "  %-26s FAIL\n" "$name"
    printf "      actual:   %s\n" "$actual"
    printf "      expected: %s\n" "$expected"
    return 1
  fi
}

FAILED=0
run_case "empty"           "[]" || FAILED=1
run_case "single"          "[100]" || FAILED=1
run_case "three"           "[100, 101, 102]" || FAILED=1
run_case "five"            "[10, 20, 30, 40, 50]" || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: chain_block_hashes_commitment matches Python keccak256(concat(block_hashes))"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
