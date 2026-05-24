#!/usr/bin/env bash
# codegen-zisk-mpt-two-leaf-root-indexed-check.sh -- PR-K170.
#
# MPT root for an indexed 2-entry trie (keys rlp(0), rlp(1)).
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

echo "==> emit zisk_mpt_two_leaf_root_indexed ELF"
lake exe codegen --program zisk_mpt_two_leaf_root_indexed --halt linux93 \
  -o gen-out/zisk_mpt_two_leaf_root_indexed

REPO_ROOT="$(pwd)"

# run_case <name> <value_0_hex> <value_1_hex>
run_case() {
  local name="$1" v0="$2" v1="$3"

  local in_file="$REPO_ROOT/gen-out/zisk_mpt_two_leaf_root_indexed_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_mpt_two_leaf_root_indexed_${name}.output"
  local exp_hex_file="$REPO_ROOT/gen-out/zisk_mpt_two_leaf_root_indexed_${name}.expected.hex"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys, rlp
try:
    from Crypto.Hash import keccak
    def keccak256(b):
        h = keccak.new(digest_bits=256); h.update(b); return h.digest()
except Exception:
    import sha3
    def keccak256(b): return sha3.keccak_256(b).digest()

v0 = bytes.fromhex('$v0')
v1 = bytes.fromhex('$v1')

# Build the MPT root by walking the standard algorithm.
# Inline the logic here for portability (rather than depending on
# execution-specs' Python trie module).
import rlp as _rlp

# Each leaf: HP-encode(suffix nibbles, is_leaf=True) + value.
def hp_leaf(nibbles, value):
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
    return _rlp.encode([bytes(hp), value])

def slot_ref(node_rlp):
    if len(node_rlp) < 32:
        return node_rlp
    return b'\\xa0' + keccak256(node_rlp)

# rlp(0)=0x80 -> nibbles [8, 0]; suffix after cpl=0 is [0]
leaf_0 = hp_leaf([0], v0)
# rlp(1)=0x01 -> nibbles [0, 1]; suffix after cpl=0 is [1]
leaf_1 = hp_leaf([1], v1)

slot_0 = slot_ref(leaf_0)  # goes at branch slot 8
slot_1 = slot_ref(leaf_1)  # goes at branch slot 0

slots = [b'\\x80'] * 17
slots[8] = slot_0
slots[0] = slot_1
branch_rlp = _rlp.encode([s for s in slots])  # 17-list

# Actually rlp.encode([...]) treats each entry as an item -- but
# our slots are already RLP items (some are raw RLP, some are
# 0xa0|hash strings, some are 0x80 empty). For the encode to work,
# we wrap each slot as either a bytes object or pre-RLP'd item.
# Hand-build the encoding instead to avoid double-wrapping:
payload = b''.join(slots)
n = len(payload)
if n < 56:
    prefix = bytes([0xc0 + n])
else:
    n_bytes = n.to_bytes((n.bit_length() + 7) // 8, 'big')
    prefix = bytes([0xf7 + len(n_bytes)]) + n_bytes
branch_node_rlp = prefix + payload
expected = keccak256(branch_node_rlp)

with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(v0)))
    f.write(struct.pack('<Q', len(v1)))
    f.write(v0)
    f.write(v1)
    pad = (-(16 + len(v0) + len(v1))) % 8
    if pad: f.write(b'\x00' * pad)
with open(sys.argv[2], 'w') as f:
    f.write(expected.hex())
" "$in_file" "$exp_hex_file"

  "$ZISKEMU" -e gen-out/zisk_mpt_two_leaf_root_indexed.elf \
    -i "$in_file" -o "$out_file" -n 5000000 \
    >"$REPO_ROOT/gen-out/zisk_mpt_two_leaf_root_indexed_${name}.emu.log" 2>&1 || true

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

# Standard legacy tx (>= 32 bytes; will be hashed in the trie).
TX_LEGACY="f8500184ee6b280082520894aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa881bc16d674ec80000801ba01111111111111111111111111111111111111111111111111111111111111111a02222222222222222222222222222222222222222222222222222222222222222"
# A second legacy tx
TX_LEGACY_2="f8500284ee6b280082520894bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb881bc16d674ec80000801ba03333333333333333333333333333333333333333333333333333333333333333a04444444444444444444444444444444444444444444444444444444444444444"

FAILED=0
# Two minimal tx values (small, hashed)
run_case "two_legacy_txs"      "$TX_LEGACY"  "$TX_LEGACY_2" || FAILED=1
# Two minimal short values (inline path)
run_case "two_short_values"    "01"          "02"           || FAILED=1
# Mix: short value + long value
run_case "short_and_long"      "01"          "$TX_LEGACY"   || FAILED=1
# Two empty values
run_case "two_empty_values"    ""            ""             || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: mpt_two_leaf_root_indexed matches Python keccak256(rlp(branch([slot0,...])))"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
