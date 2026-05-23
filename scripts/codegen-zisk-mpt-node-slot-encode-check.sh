#!/usr/bin/env bash
# codegen-zisk-mpt-node-slot-encode-check.sh -- PR-K163.
#
# Given a child MPT node's RLP, produce the parent-slot bytes:
#   inline (len < 32): node_rlp verbatim
#   hashed (len >= 32): 0xa0 || keccak256(node_rlp)
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

echo "==> emit zisk_mpt_node_slot_encode ELF"
lake exe codegen --program zisk_mpt_node_slot_encode --halt linux93 \
  -o gen-out/zisk_mpt_node_slot_encode

REPO_ROOT="$(pwd)"

# run_case <name> <node_rlp_hex>
run_case() {
  local name="$1" node_rlp="$2"

  local in_file="$REPO_ROOT/gen-out/zisk_mpt_node_slot_encode_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_mpt_node_slot_encode_${name}.output"
  local exp_hex_file="$REPO_ROOT/gen-out/zisk_mpt_node_slot_encode_${name}.expected.hex"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys
try:
    from Crypto.Hash import keccak
    def keccak256(b):
        h = keccak.new(digest_bits=256); h.update(b); return h.digest()
except Exception:
    import sha3
    def keccak256(b): return sha3.keccak_256(b).digest()

node_rlp = bytes.fromhex('$node_rlp')
if len(node_rlp) < 32:
    expected = node_rlp
else:
    expected = b'\\xa0' + keccak256(node_rlp)

with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(node_rlp)))
    f.write(node_rlp)
    pad = (-(8 + len(node_rlp))) % 8
    if pad: f.write(b'\x00' * pad)
with open(sys.argv[2], 'w') as f:
    f.write(expected.hex())
" "$in_file" "$exp_hex_file"

  "$ZISKEMU" -e gen-out/zisk_mpt_node_slot_encode.elf \
    -i "$in_file" -o "$out_file" -n 1000000 \
    >"$REPO_ROOT/gen-out/zisk_mpt_node_slot_encode_${name}.emu.log" 2>&1 || true

  local actual_status; actual_status="$(xxd -p -l 8 "$out_file" | tr -d '\n')"
  local actual_len_le; actual_len_le="$(dd if="$out_file" bs=1 skip=8 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local actual_len; actual_len="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$actual_len_le'))[0])")"
  local expected_hex; expected_hex="$(cat "$exp_hex_file")"
  local expected_len; expected_len=$(( ${#expected_hex} / 2 ))
  local actual_hex; actual_hex="$(dd if="$out_file" bs=1 skip=16 count="$expected_len" 2>/dev/null | xxd -p | tr -d '\n')"

  if [[ "$actual_status" == "0000000000000000" \
       && "$actual_len" == "$expected_len" \
       && "$actual_hex" == "$expected_hex" ]]; then
    local mode="inline"
    [[ "$expected_len" == "33" ]] && mode="hashed"
    printf "  %-30s OK   mode=%s len=%d\n" "$name" "$mode" "$expected_len"
    return 0
  else
    printf "  %-30s FAIL status=0x%s actual_len=%d expected_len=%d\n" "$name" "$actual_status" "$actual_len" "$expected_len"
    printf "      actual:   %s\n" "$actual_hex"
    printf "      expected: %s\n" "$expected_hex"
    return 1
  fi
}

FAILED=0
# Inline cases (len < 32)
run_case "empty_string"        "80"                       || FAILED=1
run_case "short_5b"            "85deadbeef00"             || FAILED=1
run_case "ten_byte_list"       "c401020304"               || FAILED=1
run_case "len_31"              "$(python3 -c "print('9f' + 'ab'*30)")" || FAILED=1
# Boundary: len == 32 -> hashed
run_case "len_32"              "$(python3 -c "print('ab' * 32)")"     || FAILED=1
# Hashed cases
run_case "hashed_64b"          "$(python3 -c "print('cd' * 64)")"     || FAILED=1
run_case "hashed_128b"         "$(python3 -c "print('ef' * 128)")"    || FAILED=1
# Realistic short leaf node (from K162 fixtures)
run_case "single_leaf_short"   "c4820080"                              || FAILED=1
# Realistic long leaf node
run_case "tx_index_0_leaf"     "f8550184ee6b280082520894aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa881bc16d674ec80000801ba01111111111111111111111111111111111111111111111111111111111111111a02222222222222222222222222222222222222222222222222222222222222222" || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: mpt_node_slot_encode picks inline / hashed correctly per spec"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
