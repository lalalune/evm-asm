#!/usr/bin/env bash
# codegen-zisk-tx-signing-hash-legacy-eip155-check.sh -- PR-K146.
#
# Legacy EIP-155 signing hash:
#   keccak256(rlp([nonce, gas_price, gas_limit, to, value, data, chain_id, 0, 0]))
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

echo "==> emit zisk_tx_signing_hash_legacy_eip155 ELF"
lake exe codegen --program zisk_tx_signing_hash_legacy_eip155 --halt linux93 \
  -o gen-out/zisk_tx_signing_hash_legacy_eip155

REPO_ROOT="$(pwd)"

# run_case <name> <chain_id> <nonce> <to_hex_or_empty>
run_case() {
  local name="$1" cid="$2" nonce="$3" to="$4"

  local in_file="$REPO_ROOT/gen-out/zisk_tx_signing_hash_legacy_eip155_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_tx_signing_hash_legacy_eip155_${name}.output"
  local exp_hex_file="$REPO_ROOT/gen-out/zisk_tx_signing_hash_legacy_eip155_${name}.expected.hex"

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
to_hex = '$to'
to = bytes.fromhex(to_hex) if to_hex else b''
# EIP-155 form: v = chain_id*2 + 35 (or +36); for the signing hash itself
# v/r/s are zero, but the full tx contains the real v/r/s. We're using
# the *full* legacy tx as input and the helper splices out v/r/s.
v = cid * 2 + 35
r = int.from_bytes(bytes([0x11]*32), 'big')
s = int.from_bytes(bytes([0x22]*32), 'big')
full_tx = [nonce, 10**9, 21000, to, 10**18, b'', v, r, s]
tx_rlp = rlp.encode(full_tx)
signing_body = [nonce, 10**9, 21000, to, 10**18, b'', cid, 0, 0]
expected = keccak256(rlp.encode(signing_body))
with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(tx_rlp)))
    f.write(struct.pack('<Q', cid))
    f.write(tx_rlp)
    pad = (-(16 + len(tx_rlp))) % 8
    if pad: f.write(b'\x00' * pad)
with open(sys.argv[2], 'w') as f:
    f.write(expected.hex())
" "$in_file" "$exp_hex_file"

  "$ZISKEMU" -e gen-out/zisk_tx_signing_hash_legacy_eip155.elf \
    -i "$in_file" -o "$out_file" -n 5000000 \
    >"$REPO_ROOT/gen-out/zisk_tx_signing_hash_legacy_eip155_${name}.emu.log" 2>&1 || true

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

ALICE="aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"

FAILED=0
# Mainnet chain_id (1) — most common case.
run_case "mainnet_value_transfer"    1   42      "$ALICE" || FAILED=1
# Sepolia (11155111) — chain_id large enough to require multi-byte RLP.
run_case "sepolia_value_transfer"    11155111 99 "$ALICE" || FAILED=1
# nonce=0 (first tx)
run_case "mainnet_nonce_zero"        1   0       "$ALICE" || FAILED=1
# chain_id=128 (boundary: needs 0x81 0x80 in RLP)
run_case "chain_id_128"              128 1       "$ALICE" || FAILED=1
# chain_id=256 (multi-byte)
run_case "chain_id_256"              256 1       "$ALICE" || FAILED=1
# chain_id=large u64
run_case "chain_id_large"            1099511627775 7 "$ALICE" || FAILED=1
# Contract-creation (to is empty)
run_case "creation_tx"               1   3       "" || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: tx_signing_hash_legacy_eip155 matches keccak256(rlp([fields0..5, cid, 0, 0]))"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
