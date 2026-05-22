#!/usr/bin/env bash
# codegen-zisk-account-validate-code-hash-check.sh -- PR-K98.
#
# Verify account.code_hash == keccak256(claimed_code).
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

echo "==> emit zisk_account_validate_code_hash ELF"
lake exe codegen --program zisk_account_validate_code_hash --halt linux93 \
  -o gen-out/zisk_account_validate_code_hash

REPO_ROOT="$(pwd)"

# run_case <name> <code_hex> <claimed_hex> <expected_status>
run_case() {
  local name="$1" code="$2" claimed="$3" exp="$4"

  local in_file="$REPO_ROOT/gen-out/zisk_account_validate_code_hash_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_account_validate_code_hash_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys, rlp
from Crypto.Hash import keccak
code = bytes.fromhex('$code')
claimed = bytes.fromhex('$claimed')
code_hash = keccak.new(digest_bits=256).update(code).digest()
account = [
    0,                     # nonce
    10**18,                # balance
    bytes([0x88]*32),      # storage_root
    code_hash,             # code_hash
]
account_rlp = rlp.encode(account)
with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(account_rlp)))
    f.write(struct.pack('<Q', len(claimed)))
    f.write(account_rlp)
    f.write(claimed)
    total = 16 + len(account_rlp) + len(claimed)
    pad = (-total) % 8
    if pad: f.write(b'\x00' * pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_account_validate_code_hash.elf \
    -i "$in_file" -o "$out_file" -n 5000000 \
    >"$REPO_ROOT/gen-out/zisk_account_validate_code_hash_${name}.emu.log" 2>&1 || true

  local actual_status; actual_status="$(xxd -p -l 8 "$out_file" | tr -d '\n')"
  local exp_status_le; exp_status_le="$(python3 -c "print(int('$exp').to_bytes(8, 'little').hex())")"

  if [[ "$actual_status" == "$exp_status_le" ]]; then
    printf "  %-32s OK   status=%d\n" "$name" "$exp"
    return 0
  else
    printf "  %-32s FAIL status=0x%s expected=%d\n" "$name" "$actual_status" "$exp"
    return 1
  fi
}

# Some sample bytecode
TINY_CONTRACT="6080604052348015600f57600080fd5b50603f80601d6000396000f3fe"
LONG_CONTRACT="$(python3 -c "print('60' + 'aabbccdd' * 100)")"

FAILED=0
# EOA: empty code, account.code_hash = keccak256(b'') — claimed empty
run_case "eoa_empty_match"          ""              ""              0 || FAILED=1
# Contract: code = tiny, account.code_hash = keccak256(tiny) — claimed = tiny
run_case "tiny_contract_match"      "$TINY_CONTRACT" "$TINY_CONTRACT" 0 || FAILED=1
# Contract: long code, match
run_case "long_contract_match"      "$LONG_CONTRACT" "$LONG_CONTRACT" 0 || FAILED=1
# Single byte: code = 0x00, match
run_case "single_byte_match"        "00"            "00"            0 || FAILED=1
# Mismatch: account.code_hash for tiny, but caller claims empty
run_case "tiny_vs_empty"            "$TINY_CONTRACT" ""              2 || FAILED=1
# Mismatch: account.code_hash for empty, but caller claims tiny
run_case "empty_vs_tiny"            ""              "$TINY_CONTRACT" 2 || FAILED=1
# Mismatch: same length, different content
run_case "different_same_length"    "aabbccdd"      "ddccbbaa"      2 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: account_validate_code_hash matches code_hash to keccak256(code)"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
