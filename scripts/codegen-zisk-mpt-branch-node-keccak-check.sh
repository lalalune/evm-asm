#!/usr/bin/env bash
# codegen-zisk-mpt-branch-node-keccak-check.sh -- PR-K169.
#
# Compute keccak256(rlp(branch_payload)) for a pre-concatenated
# 17-slot payload.
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

echo "==> emit zisk_mpt_branch_node_keccak ELF"
lake exe codegen --program zisk_mpt_branch_node_keccak --halt linux93 \
  -o gen-out/zisk_mpt_branch_node_keccak

REPO_ROOT="$(pwd)"

# run_case <name> <slot_payload_hex>
# slot_payload is the pre-concatenated 17-slot bytes.
run_case() {
  local name="$1" payload="$2"

  local in_file="$REPO_ROOT/gen-out/zisk_mpt_branch_node_keccak_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_mpt_branch_node_keccak_${name}.output"
  local exp_hex_file="$REPO_ROOT/gen-out/zisk_mpt_branch_node_keccak_${name}.expected.hex"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys
try:
    from Crypto.Hash import keccak
    def keccak256(b):
        h = keccak.new(digest_bits=256); h.update(b); return h.digest()
except Exception:
    import sha3
    def keccak256(b): return sha3.keccak_256(b).digest()

payload = bytes.fromhex('$payload')
n = len(payload)
if n < 56:
    prefix = bytes([0xc0 + n])
else:
    n_bytes = n.to_bytes((n.bit_length() + 7) // 8, 'big')
    prefix = bytes([0xf7 + len(n_bytes)]) + n_bytes
branch_node_rlp = prefix + payload
expected = keccak256(branch_node_rlp)

with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', n))
    f.write(payload)
    pad = (-(8 + n)) % 8
    if pad: f.write(b'\x00' * pad)
with open(sys.argv[2], 'w') as f:
    f.write(expected.hex())
" "$in_file" "$exp_hex_file"

  "$ZISKEMU" -e gen-out/zisk_mpt_branch_node_keccak.elf \
    -i "$in_file" -o "$out_file" -n 5000000 \
    >"$REPO_ROOT/gen-out/zisk_mpt_branch_node_keccak_${name}.emu.log" 2>&1 || true

  local actual; actual="$(xxd -p -l 32 "$out_file" | tr -d '\n')"
  local expected; expected="$(cat "$exp_hex_file")"

  if [[ "$actual" == "$expected" ]]; then
    printf "  %-30s OK   root=%s...\n" "$name" "${actual:0:16}"
    return 0
  else
    printf "  %-30s FAIL\n" "$name"
    printf "      actual:   %s\n" "$actual"
    printf "      expected: %s\n" "$expected"
    return 1
  fi
}

# Helper: construct a 17-slot payload string.
ALL_EMPTY="$(python3 -c "print('80' * 17)")"

# Hashed entry at slot 0 (33-byte 0xa0 + 32B hash), rest empty.
HASH32_A="a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0"
HASH32_B="b0b1b2b3b4b5b6b7b8b9babbbcbdbebfc0c1c2c3c4c5c6c7c8c9cacbcccdcecf"
ONE_HASH_AT_0="$(python3 -c "
import json
slots = ['80']*17
slots[0] = 'a0' + '$HASH32_A'
print(''.join(slots))
")"

# Realistic 2-tx-block divergence: slots 0 and 8 hashed.
TWO_TX_DIVERGENCE="$(python3 -c "
slots = ['80']*17
slots[0] = 'a0' + '$HASH32_A'
slots[8] = 'a0' + '$HASH32_B'
print(''.join(slots))
")"

INLINE_AT_3="$(python3 -c "
slots = ['80']*17
slots[3] = 'c4820080'
print(''.join(slots))
")"

FAILED=0
run_case "all_empty_branch"       "$ALL_EMPTY"           || FAILED=1
run_case "one_hashed_slot0"       "$ONE_HASH_AT_0"       || FAILED=1
run_case "two_tx_divergence"      "$TWO_TX_DIVERGENCE"   || FAILED=1
run_case "inline_at_3"            "$INLINE_AT_3"         || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: mpt_branch_node_keccak matches keccak256(rlp(branch_payload))"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
