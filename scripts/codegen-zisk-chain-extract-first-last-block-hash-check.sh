#!/usr/bin/env bash
# codegen-zisk-chain-extract-first-last-block-hash-check.sh -- PR-K251.
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

echo "==> emit zisk_chain_extract_first_last_block_hash ELF"
lake exe codegen --program zisk_chain_extract_first_last_block_hash --halt linux93 \
  -o gen-out/zisk_chain_extract_first_last_block_hash

REPO_ROOT="$(pwd)"

run_case() {
  local name="$1" timestamps="$2" exp_status="$3"

  local in_file="$REPO_ROOT/gen-out/zisk_chain_extract_first_last_block_hash_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_chain_extract_first_last_block_hash_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys, rlp
from ethereum_types.bytes import Bytes32
try:
    from ethereum.crypto.hash import keccak256
except ImportError:
    from hashlib import sha3_256 as keccak256_impl
    def keccak256(data): return type('H', (), {'__bytes__': lambda s: keccak256_impl(data).digest()})()

def u_be(n):
    if n == 0: return b''
    return n.to_bytes((n.bit_length() + 7) // 8, 'big')

def make_header(ts):
    return rlp.encode([
        b'\\xa1'*32, b'\\xa2'*32, b'\\xa3'*20, b'\\xa4'*32, b'\\xa5'*32,
        b'\\xa6'*32, b'\\x00'*256, b'', b'\\x01', b'\\x83\\xff\\xff\\xff',
        b'', u_be(ts), b'', b'\\xa7'*32, b'\\x00'*8,
    ])

ts_list = $timestamps
headers = [make_header(t) for t in ts_list]
N = len(headers)
lengths = b''.join(struct.pack('<Q', len(h)) for h in headers)
flat = b''.join(headers)

# Compute expected hashes (Python's hashlib keccak256 via pycryptodome or eth_utils)
try:
    from eth_utils import keccak
except ImportError:
    from Crypto.Hash import keccak as kc
    def keccak(b):
        k = kc.new(digest_bits=256); k.update(b); return k.digest()

first_hash = keccak(headers[0]).hex() if headers else '00'*32
last_hash = keccak(headers[-1]).hex() if headers else '00'*32

# Write input
with open(sys.argv[1], 'wb') as f:
    record = struct.pack('<Q', N) + lengths + flat
    f.write(record)
    pad = (-len(record)) % 8
    if pad: f.write(b'\x00' * pad)

# Stash expected for shell to read
with open(sys.argv[1] + '.expected', 'w') as f:
    f.write(f'{first_hash}\n{last_hash}\n')
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_chain_extract_first_last_block_hash.elf \
    -i "$in_file" -o "$out_file" -n 5000000 \
    >"$REPO_ROOT/gen-out/zisk_chain_extract_first_last_block_hash_${name}.emu.log" 2>&1 || true

  local s_le; s_le="$(dd if="$out_file" bs=1 skip=0  count=8  2>/dev/null | xxd -p | tr -d '\n')"
  local fr_hex; fr_hex="$(dd if="$out_file" bs=1 skip=8  count=32 2>/dev/null | xxd -p | tr -d '\n')"
  local lr_hex; lr_hex="$(dd if="$out_file" bs=1 skip=40 count=32 2>/dev/null | xxd -p | tr -d '\n')"
  local status
  status="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$s_le'))[0])")"

  local exp_first exp_last
  exp_first="$(sed -n '1p' "$in_file.expected")"
  exp_last="$(sed -n '2p' "$in_file.expected")"

  if [[ "$status" == "$exp_status" ]]; then
    if [[ "$exp_status" == "0" ]]; then
      if [[ "$fr_hex" == "$exp_first" && "$lr_hex" == "$exp_last" ]]; then
        printf "  %-26s OK   status=%s first=%s.. last=%s..\n" "$name" "$status" "${fr_hex:0:16}" "${lr_hex:0:16}"
        return 0
      else
        printf "  %-26s FAIL hashes mismatch\n" "$name"
        printf "    first got %s\n    first exp %s\n" "$fr_hex" "$exp_first"
        printf "    last  got %s\n    last  exp %s\n" "$lr_hex" "$exp_last"
        return 1
      fi
    fi
    printf "  %-26s OK   status=%s\n" "$name" "$status"
    return 0
  else
    printf "  %-26s FAIL status=%s/%s\n" "$name" "$status" "$exp_status"
    return 1
  fi
}

FAILED=0
run_case "empty"         "[]"                 1 || FAILED=1
run_case "single"        "[1700000000]"       0 || FAILED=1
run_case "two"           "[1000, 2000]"       0 || FAILED=1
run_case "three"         "[1000, 2000, 3000]" 0 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: chain_extract_first_last_block_hash returns (first, last) keccak256(header)"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
