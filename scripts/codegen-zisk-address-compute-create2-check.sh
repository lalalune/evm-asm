#!/usr/bin/env bash
# codegen-zisk-address-compute-create2-check.sh -- PR-K126.
#
# CREATE2 contract address per EIP-1014.
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

echo "==> emit zisk_address_compute_create2 ELF"
lake exe codegen --program zisk_address_compute_create2 --halt linux93 \
  -o gen-out/zisk_address_compute_create2

REPO_ROOT="$(pwd)"

# run_case <name> <sender_hex> <salt_hex> <init_code_hex>
run_case() {
  local name="$1" sender="$2" salt="$3" code="$4"

  local in_file="$REPO_ROOT/gen-out/zisk_address_compute_create2_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_address_compute_create2_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys
from Crypto.Hash import keccak
sender = bytes.fromhex('$sender')
salt   = bytes.fromhex('$salt')
code   = bytes.fromhex('$code')
assert len(sender) == 20
assert len(salt) == 32

inner = keccak.new(digest_bits=256).update(code).digest()
preimage = b'\xff' + sender + salt + inner
outer = keccak.new(digest_bits=256).update(preimage).digest()
addr = outer[-20:]

with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(code)))
    f.write(sender)
    f.write(salt)
    f.write(code)
    pad = (-(8 + 20 + 32 + len(code))) % 8
    if pad: f.write(b'\x00' * pad)
with open(sys.argv[1] + '.expected', 'wb') as f:
    f.write(addr)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_address_compute_create2.elf \
    -i "$in_file" -o "$out_file" -n 5000000 \
    >"$REPO_ROOT/gen-out/zisk_address_compute_create2_${name}.emu.log" 2>&1 || true

  local actual_status; actual_status="$(xxd -p -l 8 "$out_file" | tr -d '\n')"
  local actual_addr; actual_addr="$(dd if="$out_file" bs=1 skip=8 count=20 2>/dev/null | xxd -p | tr -d '\n')"
  local expected_addr; expected_addr="$(xxd -p "$in_file.expected" | tr -d '\n')"

  if [[ "$actual_status" == "0000000000000000" && "$actual_addr" == "$expected_addr" ]]; then
    printf "  %-32s OK   addr=0x%s..\n" "$name" "${actual_addr:0:12}"
    return 0
  else
    printf "  %-32s FAIL\n    expected: %s\n    actual:   %s\n" "$name" "$expected_addr" "$actual_addr"
    return 1
  fi
}

# EIP-1014 example fixtures from the EIP spec
FAILED=0
run_case "eip1014_ex0" \
  "0000000000000000000000000000000000000000" \
  "0000000000000000000000000000000000000000000000000000000000000000" \
  "00" || FAILED=1

run_case "eip1014_ex1" \
  "deadbeef00000000000000000000000000000000" \
  "0000000000000000000000000000000000000000000000000000000000000000" \
  "00" || FAILED=1

run_case "eip1014_ex2" \
  "deadbeef00000000000000000000000000000000" \
  "000000000000000000000000feed000000000000000000000000000000000000" \
  "00" || FAILED=1

run_case "eip1014_ex3" \
  "0000000000000000000000000000000000000000" \
  "0000000000000000000000000000000000000000000000000000000000000000" \
  "deadbeef" || FAILED=1

run_case "eip1014_ex4" \
  "00000000000000000000000000000000deadbeef" \
  "00000000000000000000000000000000000000000000000000000000cafebabe" \
  "deadbeef" || FAILED=1

run_case "eip1014_ex5" \
  "00000000000000000000000000000000deadbeef" \
  "00000000000000000000000000000000000000000000000000000000cafebabe" \
  "deadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef" || FAILED=1

# Long init code
run_case "long_init_code" \
  "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa" \
  "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" \
  "$(python3 -c "print('60' * 300)")" || FAILED=1

# Empty init code
run_case "empty_init_code" \
  "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa" \
  "0000000000000000000000000000000000000000000000000000000000000000" \
  "" || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: address_compute_create2 matches EIP-1014"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
