#!/usr/bin/env bash
# codegen-zisk-mpt-leaf-node-encode-from-nibbles-check.sh -- PR-K168.
#
# Encode an MPT leaf node from nibble-input path + raw value.
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

echo "==> emit zisk_mpt_leaf_node_encode_from_nibbles ELF"
lake exe codegen --program zisk_mpt_leaf_node_encode_from_nibbles --halt linux93 \
  -o gen-out/zisk_mpt_leaf_node_encode_from_nibbles

REPO_ROOT="$(pwd)"

# run_case <name> <nibbles_hex> <value_hex>
# nibbles_hex: one byte per nibble (low 4 bits)
run_case() {
  local name="$1" nibs="$2" val="$3"

  local in_file="$REPO_ROOT/gen-out/zisk_mpt_leaf_node_encode_from_nibbles_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_mpt_leaf_node_encode_from_nibbles_${name}.output"
  local exp_hex_file="$REPO_ROOT/gen-out/zisk_mpt_leaf_node_encode_from_nibbles_${name}.expected.hex"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys, rlp
nibbles_bytes = bytes.fromhex('$nibs')
nibbles = list(nibbles_bytes)
val = bytes.fromhex('$val')

# HP-encode with is_leaf=true.
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
    f.write(struct.pack('<Q', len(nibbles)))
    f.write(struct.pack('<Q', len(val)))
    f.write(bytes(nibbles))
    f.write(val)
    pad = (-(16 + len(nibbles) + len(val))) % 8
    if pad: f.write(b'\x00' * pad)
with open(sys.argv[2], 'w') as f:
    f.write(leaf_node_rlp.hex())
" "$in_file" "$exp_hex_file"

  "$ZISKEMU" -e gen-out/zisk_mpt_leaf_node_encode_from_nibbles.elf \
    -i "$in_file" -o "$out_file" -n 1000000 \
    >"$REPO_ROOT/gen-out/zisk_mpt_leaf_node_encode_from_nibbles_${name}.emu.log" 2>&1 || true

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
    printf "  %-30s OK   nibs=%d len=%d\n" "$name" $(( ${#nibs} / 2 )) "$expected_len"
    return 0
  else
    printf "  %-30s FAIL status=0x%s actual_len=%d expected_len=%d\n" "$name" "$actual_status" "$actual_len" "$expected_len"
    printf "      actual:   %s...\n" "${actual_hex:0:80}"
    printf "      expected: %s...\n" "${expected_prefix:0:80}"
    return 1
  fi
}

FAILED=0
# Even-count nibbles
run_case "even_2nib"          "0008" "deadbeef" || FAILED=1
# Odd-count nibbles
run_case "odd_1nib"           "08"   "deadbeef" || FAILED=1
# Empty path (degenerate but legal)
run_case "empty_path"         ""     "cafebabe" || FAILED=1
# Mirror of K162 tx_index_0 case (nibbles [8,0] = bytes_to_nibbles(0x80))
run_case "tx_index_0_suffix"  "0800" "f8500184ee6b280082520894aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa881bc16d674ec80000801ba01111111111111111111111111111111111111111111111111111111111111111a02222222222222222222222222222222222222222222222222222222222222222" || FAILED=1
# Single-nibble suffix (typical for divergence-leaf inside a branch)
run_case "single_nibble_leaf" "01"   "63"       || FAILED=1
# 63-nibble path (state-trie depth minus shared prefix)
run_case "long_path"          "$(python3 -c "print('0a' * 63)")" "deadbeef" || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: mpt_leaf_node_encode_from_nibbles matches rlp + HP-encode (nibble input)"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
