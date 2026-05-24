#!/usr/bin/env bash
# codegen-zisk-mpt-one-leaf-root-indexed-check.sh -- PR-K185.
#
# MPT root for an indexed 1-entry trie (key rlp(0)=0x80).
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

echo "==> emit zisk_mpt_one_leaf_root_indexed ELF"
lake exe codegen --program zisk_mpt_one_leaf_root_indexed --halt linux93 \
  -o gen-out/zisk_mpt_one_leaf_root_indexed

REPO_ROOT="$(pwd)"

# run_case <name> <value_hex>
run_case() {
  local name="$1" v="$2"

  local in_file="$REPO_ROOT/gen-out/zisk_mpt_one_leaf_root_indexed_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_mpt_one_leaf_root_indexed_${name}.output"
  local exp_hex_file="$REPO_ROOT/gen-out/zisk_mpt_one_leaf_root_indexed_${name}.expected.hex"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys, rlp
try:
    from Crypto.Hash import keccak
    def keccak256(b):
        h = keccak.new(digest_bits=256); h.update(b); return h.digest()
except Exception:
    import sha3
    def keccak256(b): return sha3.keccak_256(b).digest()

v = bytes.fromhex('$v')

# Single-leaf MPT: key=rlp(0)=0x80 -> nibbles [8, 0]; suffix = full nibble seq
def hp_leaf(nibbles, value):
    flag = 2 + (len(nibbles) & 1)
    hp = bytearray()
    if len(nibbles) % 2 == 1:
        hp.append((flag << 4) | nibbles[0]); i = 1
    else:
        hp.append(flag << 4); i = 0
    while i < len(nibbles):
        hp.append((nibbles[i] << 4) | nibbles[i+1]); i += 2
    return rlp.encode([bytes(hp), value])

leaf = hp_leaf([8, 0], v)
expected = keccak256(leaf)

with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(v)))
    f.write(v)
    pad = (-(8 + len(v))) % 8
    if pad: f.write(b'\x00' * pad)
with open(sys.argv[2], 'w') as f:
    f.write(expected.hex())
" "$in_file" "$exp_hex_file"

  "$ZISKEMU" -e gen-out/zisk_mpt_one_leaf_root_indexed.elf \
    -i "$in_file" -o "$out_file" -n 2000000 \
    >"$REPO_ROOT/gen-out/zisk_mpt_one_leaf_root_indexed_${name}.emu.log" 2>&1 || true

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

TX_LEGACY="f8500184ee6b280082520894aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa881bc16d674ec80000801ba01111111111111111111111111111111111111111111111111111111111111111a02222222222222222222222222222222222222222222222222222222222222222"

FAILED=0
run_case "single_legacy_tx"   "$TX_LEGACY"  || FAILED=1
run_case "single_short_value" "01"          || FAILED=1
run_case "single_empty_value" ""            || FAILED=1
run_case "single_32B_value"   "$(printf 'aa%.0s' {1..32})" || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: mpt_one_leaf_root_indexed matches Python keccak256(rlp(leaf))"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
