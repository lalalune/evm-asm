#!/usr/bin/env bash
# codegen-zisk-address-from-pubkey-check.sh -- PR-K99.
#
# Compute Ethereum address from secp256k1 uncompressed pubkey (64 B).
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

echo "==> emit zisk_address_from_pubkey ELF"
lake exe codegen --program zisk_address_from_pubkey --halt linux93 \
  -o gen-out/zisk_address_from_pubkey

REPO_ROOT="$(pwd)"

# run_case <name> <privkey_hex>
# Derives the secp256k1 pubkey from the privkey (eth-keys) and feeds the
# uncompressed pubkey (x ‖ y) to the helper; checks against eth-keys'
# canonical address derivation.
run_case() {
  local name="$1" priv="$2"

  local in_file="$REPO_ROOT/gen-out/zisk_address_from_pubkey_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_address_from_pubkey_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys
import coincurve
from Crypto.Hash import keccak
priv_bytes = bytes.fromhex('$priv')
pk = coincurve.PrivateKey(priv_bytes)
pub_uncompressed = pk.public_key.format(compressed=False)  # 65 bytes: 0x04 ‖ x ‖ y
assert pub_uncompressed[0] == 0x04
pub = pub_uncompressed[1:]  # 64 bytes: x ‖ y
addr_bytes = keccak.new(digest_bits=256).update(pub).digest()[-20:]
with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', 64))    # pubkey length (kept for input symmetry)
    f.write(pub)
    pad = (-(8 + 64)) % 8
    if pad: f.write(b'\x00' * pad)
with open(sys.argv[1] + '.expected', 'wb') as f:
    f.write(addr_bytes)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_address_from_pubkey.elf \
    -i "$in_file" -o "$out_file" -n 1000000 \
    >"$REPO_ROOT/gen-out/zisk_address_from_pubkey_${name}.emu.log" 2>&1 || true

  local actual_status; actual_status="$(xxd -p -l 8 "$out_file" | tr -d '\n')"
  local actual_addr; actual_addr="$(dd if="$out_file" bs=1 skip=8 count=20 2>/dev/null | xxd -p | tr -d '\n')"
  local expected_addr; expected_addr="$(xxd -p "$in_file.expected" | tr -d '\n')"

  if [[ "$actual_status" == "0000000000000000" && "$actual_addr" == "$expected_addr" ]]; then
    printf "  %-32s OK   addr=0x%s\n" "$name" "${actual_addr:0:12}.."
    return 0
  else
    printf "  %-32s FAIL  status=0x%s addr=0x%s expected=0x%s\n" "$name" "$actual_status" "$actual_addr" "$expected_addr"
    return 1
  fi
}

FAILED=0
# A few well-known test private keys
run_case "priv_1"   "0000000000000000000000000000000000000000000000000000000000000001" || FAILED=1
run_case "priv_2"   "0000000000000000000000000000000000000000000000000000000000000002" || FAILED=1
run_case "priv_aa"  "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa" || FAILED=1
# Vitalik's well-known dev key
run_case "vitalik" "c87509a1c067bbde78beb793e6fa76530b6382a4c0241e5e4a9ec0a0f44dc0d3" || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: address_from_pubkey matches eth-keys canonical derivation"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
