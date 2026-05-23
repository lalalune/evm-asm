#!/usr/bin/env bash
# codegen-zisk-single-leaf-trie-root-check.sh -- PR-K157.
#
# Compute the MPT root for a single-(key, value) trie:
#   path_nibbles = bytes_to_nibbles(key)
#   hp_path      = hp_encode_nibbles(path_nibbles, is_leaf=true)
#   leaf_node    = rlp([hp_path, value])
#   root         = keccak256(leaf_node)
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

echo "==> emit zisk_single_leaf_trie_root ELF"
lake exe codegen --program zisk_single_leaf_trie_root --halt linux93 \
  -o gen-out/zisk_single_leaf_trie_root

REPO_ROOT="$(pwd)"

# run_case <name> <key_hex> <value_hex>
run_case() {
  local name="$1" key="$2" val="$3"

  local in_file="$REPO_ROOT/gen-out/zisk_single_leaf_trie_root_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_single_leaf_trie_root_${name}.output"
  local exp_hex_file="$REPO_ROOT/gen-out/zisk_single_leaf_trie_root_${name}.expected.hex"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys, rlp
try:
    from Crypto.Hash import keccak
    def keccak256(b):
        h = keccak.new(digest_bits=256); h.update(b); return h.digest()
except Exception:
    import sha3
    def keccak256(b): return sha3.keccak_256(b).digest()

key = bytes.fromhex('$key')
val = bytes.fromhex('$val')

# Build the path nibbles, HP-encode (leaf=True).
nibbles = []
for byte in key:
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
root = keccak256(leaf_node_rlp)

with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(key)))
    f.write(struct.pack('<Q', len(val)))
    f.write(key)
    f.write(val)
    pad = (-(16 + len(key) + len(val))) % 8
    if pad: f.write(b'\x00' * pad)
with open(sys.argv[2], 'w') as f:
    f.write(root.hex())
" "$in_file" "$exp_hex_file"

  "$ZISKEMU" -e gen-out/zisk_single_leaf_trie_root.elf \
    -i "$in_file" -o "$out_file" -n 5000000 \
    >"$REPO_ROOT/gen-out/zisk_single_leaf_trie_root_${name}.emu.log" 2>&1 || true

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

FAILED=0
# transactions_root for a single-tx block: key = rlp(0) = 0x80
run_case "tx_index_0"       "80" "f8500184ee6b280082520894aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa881bc16d674ec80000801ba01111111111111111111111111111111111111111111111111111111111111111a02222222222222222222222222222222222222222222222222222222222222222" || FAILED=1

# Smallest possible key/value pair
run_case "min_key_min_value" "00" "01" || FAILED=1

# Single-byte key, single-byte value
run_case "key_42_value_99"   "2a" "63" || FAILED=1

# Multi-byte key, multi-byte value
run_case "multi_byte"        "deadbeef" "cafebabedeadbeefcafebabe" || FAILED=1

# Larger value (typical receipt size, ~64 bytes)
run_case "receipt_size_val"  "80" "$(python3 -c "print('ab' * 64)")" || FAILED=1

# 32-byte key (mirrors keccak256(address) for state-trie use)
run_case "state_trie_key"    "$(python3 -c "print('aa' * 32)")" "f8440180a056e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421a0c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470" || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: single_leaf_trie_root matches Python rlp + HP-encode + keccak256"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
