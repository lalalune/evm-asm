#!/usr/bin/env bash
# codegen-zisk-withdrawal-compute-hash-check.sh -- PR-K132.
#
# keccak256(rlp.encode(withdrawal)).
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

echo "==> emit zisk_withdrawal_compute_hash ELF"
lake exe codegen --program zisk_withdrawal_compute_hash --halt linux93 \
  -o gen-out/zisk_withdrawal_compute_hash

REPO_ROOT="$(pwd)"

# run_case <name> <index> <validator> <address_hex> <amount>
run_case() {
  local name="$1" idx="$2" val="$3" addr="$4" amt="$5"

  local in_file="$REPO_ROOT/gen-out/zisk_withdrawal_compute_hash_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_withdrawal_compute_hash_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys, rlp
from Crypto.Hash import keccak
idx = $idx; val = $val; amt = $amt
addr = bytes.fromhex('$addr')
encoded = rlp.encode([idx, val, addr, amt])
h = keccak.new(digest_bits=256).update(encoded).digest()
with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', idx))
    f.write(struct.pack('<Q', val))
    f.write(struct.pack('<Q', amt))
    f.write(b'\x00' * 8)
    f.write(addr)
    pad = (-(40 + 20)) % 8
    if pad: f.write(b'\x00' * pad)
with open(sys.argv[1] + '.expected', 'wb') as f:
    f.write(h)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_withdrawal_compute_hash.elf \
    -i "$in_file" -o "$out_file" -n 5000000 \
    >"$REPO_ROOT/gen-out/zisk_withdrawal_compute_hash_${name}.emu.log" 2>&1 || true

  local actual_status; actual_status="$(xxd -p -l 8 "$out_file" | tr -d '\n')"
  local actual_hash; actual_hash="$(dd if="$out_file" bs=1 skip=8 count=32 2>/dev/null | xxd -p | tr -d '\n')"
  local expected_hash; expected_hash="$(xxd -p "$in_file.expected" | tr -d '\n')"

  if [[ "$actual_status" == "0000000000000000" && "$actual_hash" == "$expected_hash" ]]; then
    printf "  %-32s OK   hash=%s..\n" "$name" "${actual_hash:0:16}"
    return 0
  else
    printf "  %-32s FAIL\n    expected: %s\n    actual:   %s\n" "$name" "$expected_hash" "$actual_hash"
    return 1
  fi
}

ALICE="aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
BOB="bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"
ZERO="0000000000000000000000000000000000000000"

FAILED=0
run_case "all_zero"     0     0     "$ZERO"  0                       || FAILED=1
run_case "simple"       1     1     "$ALICE" "10**9"                 || FAILED=1
run_case "typical"      42    1000  "$BOB"   "$((32 * 10**9))"       || FAILED=1
run_case "large"        65536 1024  "$ALICE" "$((1000 * 10**9))"     || FAILED=1
run_case "max_u64_all"  "(1<<64)-1" "(1<<64)-1" "$BOB" "(1<<64)-1"   || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: withdrawal_compute_hash matches keccak256(rlp.encode(withdrawal))"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
