#!/usr/bin/env bash
# codegen-zisk-eip7702-authorization-signing-hash-check.sh -- PR-K147.
#
# EIP-7702 per-authorization signing hash:
#   keccak256(0x05 || rlp([chain_id, address, nonce]))
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

echo "==> emit zisk_eip7702_authorization_signing_hash ELF"
lake exe codegen --program zisk_eip7702_authorization_signing_hash --halt linux93 \
  -o gen-out/zisk_eip7702_authorization_signing_hash

REPO_ROOT="$(pwd)"

# run_case <name> <chain_id> <nonce>
run_case() {
  local name="$1" cid="$2" nonce="$3"

  local in_file="$REPO_ROOT/gen-out/zisk_eip7702_authorization_signing_hash_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_eip7702_authorization_signing_hash_${name}.output"
  local exp_hex_file="$REPO_ROOT/gen-out/zisk_eip7702_authorization_signing_hash_${name}.expected.hex"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys, rlp
try:
    from Crypto.Hash import keccak
    def keccak256(b):
        h = keccak.new(digest_bits=256); h.update(b); return h.digest()
except Exception:
    import sha3
    def keccak256(b): return sha3.keccak_256(b).digest()

cid = $cid
nonce = $nonce
DELEGATE = bytes([0xde] * 20)
y, r, s = 1, 0x11, 0x22
auth_tuple = [cid, DELEGATE, nonce, y, r, s]
tuple_rlp = rlp.encode(auth_tuple)
expected = keccak256(bytes([0x05]) + rlp.encode([cid, DELEGATE, nonce]))
with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(tuple_rlp)))
    f.write(tuple_rlp)
    pad = (-(8 + len(tuple_rlp))) % 8
    if pad: f.write(b'\x00' * pad)
with open(sys.argv[2], 'w') as f:
    f.write(expected.hex())
" "$in_file" "$exp_hex_file"

  "$ZISKEMU" -e gen-out/zisk_eip7702_authorization_signing_hash.elf \
    -i "$in_file" -o "$out_file" -n 5000000 \
    >"$REPO_ROOT/gen-out/zisk_eip7702_authorization_signing_hash_${name}.emu.log" 2>&1 || true

  local actual_status; actual_status="$(xxd -p -l 8 "$out_file" | tr -d '\n')"
  local actual_hash;   actual_hash="$(dd if="$out_file" bs=1 skip=8 count=32 2>/dev/null | xxd -p | tr -d '\n')"
  local expected_hex;  expected_hex="$(cat "$exp_hex_file")"

  if [[ "$actual_status" == "0000000000000000" && "$actual_hash" == "$expected_hex" ]]; then
    printf "  %-30s OK   cid=%d nonce=%d hash=%s...\n" "$name" "$cid" "$nonce" "${actual_hash:0:16}"
    return 0
  else
    printf "  %-30s FAIL status=0x%s\n" "$name" "$actual_status"
    printf "      actual:   %s\n" "$actual_hash"
    printf "      expected: %s\n" "$expected_hex"
    return 1
  fi
}

FAILED=0
# Mainnet chain_id, typical
run_case "mainnet_basic"          1         42         || FAILED=1
# Sepolia chain_id (large)
run_case "sepolia"                11155111  99         || FAILED=1
# nonce=0 boundary (RLP-canonical empty)
run_case "nonce_zero"             1         0          || FAILED=1
# chain_id=0 boundary (RLP-canonical empty)
run_case "chain_zero_nonce_zero"  0         0          || FAILED=1
# Both fields requiring multi-byte RLP
run_case "chain_256_nonce_300"    256       300        || FAILED=1
# Large u64 chain_id and nonce
run_case "max_chain_max_nonce"    $((2**63 - 1)) $((2**63 - 1))  || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: eip7702_authorization_signing_hash matches keccak256(0x05 || rlp([cid, addr, nonce]))"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
