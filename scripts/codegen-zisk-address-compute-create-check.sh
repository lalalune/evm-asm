#!/usr/bin/env bash
# codegen-zisk-address-compute-create-check.sh -- PR-K127.
#
# CREATE address: keccak256(rlp.encode([sender, nonce]))[12:].
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

echo "==> emit zisk_address_compute_create ELF"
lake exe codegen --program zisk_address_compute_create --halt linux93 \
  -o gen-out/zisk_address_compute_create

REPO_ROOT="$(pwd)"

# run_case <name> <sender_hex> <nonce>
run_case() {
  local name="$1" sender="$2" nonce="$3"

  local in_file="$REPO_ROOT/gen-out/zisk_address_compute_create_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_address_compute_create_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys, rlp
from Crypto.Hash import keccak
sender = bytes.fromhex('$sender')
assert len(sender) == 20
nonce = $nonce
preimage = rlp.encode([sender, nonce])
addr = keccak.new(digest_bits=256).update(preimage).digest()[-20:]

with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', nonce))
    f.write(sender)
    pad = (-(8 + 20)) % 8
    if pad: f.write(b'\x00' * pad)
with open(sys.argv[1] + '.expected', 'wb') as f:
    f.write(addr)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_address_compute_create.elf \
    -i "$in_file" -o "$out_file" -n 5000000 \
    >"$REPO_ROOT/gen-out/zisk_address_compute_create_${name}.emu.log" 2>&1 || true

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

ALICE="aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
BOB="bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"

FAILED=0
# Cover all nonce-RLP branches:
# nonce == 0 (single 0x80)
run_case "nonce_zero"          "$ALICE"  0      || FAILED=1
# 1..127 (single byte)
run_case "nonce_1"             "$ALICE"  1      || FAILED=1
run_case "nonce_127"           "$ALICE"  127    || FAILED=1
# 128..255 (0x81 || 1B)
run_case "nonce_128"           "$ALICE"  128    || FAILED=1
run_case "nonce_255"           "$ALICE"  255    || FAILED=1
# 256..65535 (0x82 || 2B)
run_case "nonce_256"           "$ALICE"  256    || FAILED=1
run_case "nonce_65535"         "$ALICE"  65535  || FAILED=1
# 3..4-byte nonces
run_case "nonce_65536"         "$BOB"    65536  || FAILED=1
run_case "nonce_1000000"       "$BOB"    1000000 || FAILED=1
# Near u64 max
run_case "nonce_huge"          "$ALICE"  "(1 << 56) - 1" || FAILED=1
run_case "nonce_max"           "$ALICE"  "(1 << 64) - 1" || FAILED=1
# Zero sender
run_case "zero_sender"         "0000000000000000000000000000000000000000" 0 || FAILED=1
# Sender with random pattern
run_case "interesting_sender"  "1234567890abcdef1234567890abcdef12345678" 42 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: address_compute_create matches keccak256(rlp([sender, nonce]))[12:]"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
