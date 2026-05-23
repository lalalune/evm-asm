#!/usr/bin/env bash
# codegen-zisk-mpt-leaf-node-encode-check.sh -- PR-K162.
#
# Encode an MPT leaf node as RLP (without keccak'ing): the step
# before the final keccak inside PR-K157 single_leaf_trie_root.
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

echo "==> emit zisk_mpt_leaf_node_encode ELF"
lake exe codegen --program zisk_mpt_leaf_node_encode --halt linux93 \
  -o gen-out/zisk_mpt_leaf_node_encode

REPO_ROOT="$(pwd)"

# run_case <name> <path_hex> <value_hex>
run_case() {
  local name="$1" path="$2" val="$3"

  local in_file="$REPO_ROOT/gen-out/zisk_mpt_leaf_node_encode_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_mpt_leaf_node_encode_${name}.output"
  local exp_hex_file="$REPO_ROOT/gen-out/zisk_mpt_leaf_node_encode_${name}.expected.hex"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys, rlp
path = bytes.fromhex('$path')
val = bytes.fromhex('$val')
# HP-encode (leaf=true).
nibbles = []
for byte in path:
    nibbles.append(byte >> 4)
    nibbles.append(byte & 0xf)
flag = 2 + (len(nibbles) & 1)
hp = bytearray()
if len(nibbles) % 2 == 1:
    hp.append((flag << 4) | nibbles[0])
    i = 1
else:
    hp.append(flag << 4)
    i = 0
while i < len(nibbles):
    hp.append((nibbles[i] << 4) | nibbles[i+1])
    i += 2
leaf_node_rlp = rlp.encode([bytes(hp), val])

with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(path)))
    f.write(struct.pack('<Q', len(val)))
    f.write(path)
    f.write(val)
    pad = (-(16 + len(path) + len(val))) % 8
    if pad: f.write(b'\x00' * pad)
with open(sys.argv[2], 'w') as f:
    f.write(leaf_node_rlp.hex())
" "$in_file" "$exp_hex_file"

  "$ZISKEMU" -e gen-out/zisk_mpt_leaf_node_encode.elf \
    -i "$in_file" -o "$out_file" -n 1000000 \
    >"$REPO_ROOT/gen-out/zisk_mpt_leaf_node_encode_${name}.emu.log" 2>&1 || true

  local actual_status; actual_status="$(xxd -p -l 8 "$out_file" | tr -d '\n')"
  local actual_len_le; actual_len_le="$(dd if="$out_file" bs=1 skip=8 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local actual_len; actual_len="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$actual_len_le'))[0])")"
  local expected_hex; expected_hex="$(cat "$exp_hex_file")"
  local expected_len; expected_len=$(( ${#expected_hex} / 2 ))
  local cmp_len=$expected_len
  if [[ $cmp_len -gt 240 ]]; then cmp_len=240; fi
  local actual_hex; actual_hex="$(dd if="$out_file" bs=1 skip=16 count="$cmp_len" 2>/dev/null | xxd -p | tr -d '\n')"
  local expected_prefix="${expected_hex:0:$((2 * cmp_len))}"

  if [[ "$actual_status" == "0000000000000000" \
       && "$actual_len" == "$expected_len" \
       && "$actual_hex" == "$expected_prefix" ]]; then
    printf "  %-30s OK   len=%d\n" "$name" "$expected_len"
    return 0
  else
    printf "  %-30s FAIL status=0x%s actual_len=%d expected_len=%d\n" "$name" "$actual_status" "$actual_len" "$expected_len"
    printf "      actual:   %s...\n" "${actual_hex:0:80}"
    printf "      expected: %s...\n" "${expected_prefix:0:80}"
    return 1
  fi
}

FAILED=0
# Single-byte path & value -- 2-nibble path
run_case "1B_path_1B_value"   "80" "01" || FAILED=1
# tx_index_0 leaf (rlp(0) key)
run_case "tx_index_0_leaf"    "80" "f8500184ee6b280082520894aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa881bc16d674ec80000801ba01111111111111111111111111111111111111111111111111111111111111111a02222222222222222222222222222222222222222222222222222222222222222" || FAILED=1
# Smallest possible
run_case "min"                "00" "01" || FAILED=1
# Multi-byte path
run_case "multi_byte_path"    "deadbeef" "cafebabedeadbeefcafebabe" || FAILED=1
# 32-byte path (state-trie-like)
run_case "state_trie_path"    "$(python3 -c "print('aa' * 32)")" "f8440180a056e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421a0c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470" || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: mpt_leaf_node_encode matches Python rlp + HP-encode (pre-keccak)"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
