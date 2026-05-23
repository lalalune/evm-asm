#!/usr/bin/env bash
# codegen-zisk-mpt-extension-extract-check.sh -- PR-K114.
#
# Decode a 2-item extension node into (nibbles, child_ref bytes).
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

echo "==> emit zisk_mpt_extension_extract ELF"
lake exe codegen --program zisk_mpt_extension_extract --halt linux93 \
  -o gen-out/zisk_mpt_extension_extract

REPO_ROOT="$(pwd)"

# run_case <name> <node_kind> <nibbles_csv> <ref_hex>
run_case() {
  local name="$1" kind="$2" nibbles_csv="$3" ref_hex="$4"

  local in_file="$REPO_ROOT/gen-out/zisk_mpt_extension_extract_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_mpt_extension_extract_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys, rlp
from ethereum.forks.amsterdam.trie import nibble_list_to_compact
kind = '$kind'
nibs_csv = '$nibbles_csv'
nibs = [int(n) for n in nibs_csv.split(',') if n.strip()] if nibs_csv else []
ref = bytes.fromhex('$ref_hex')

if kind == 'extension':
    path = nibble_list_to_compact(bytes(nibs), False)
    node = [path, ref]
elif kind == 'leaf':
    path = nibble_list_to_compact(bytes(nibs), True)
    node = [path, ref]
elif kind == 'branch':
    node = [b''] * 16 + [b'val']
elif kind == 'invalid':
    node = [b'\\x00']
else:
    raise ValueError(kind)

node_rlp = rlp.encode(node)
with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(node_rlp)))
    f.write(node_rlp)
    pad = (-(8 + len(node_rlp))) % 8
    if pad: f.write(b'\x00' * pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_mpt_extension_extract.elf \
    -i "$in_file" -o "$out_file" -n 5000000 \
    >"$REPO_ROOT/gen-out/zisk_mpt_extension_extract_${name}.emu.log" 2>&1 || true

  local actual_status; actual_status="$(xxd -p -l 8 "$out_file" | tr -d '\n')"

  if [[ "$kind" == "extension" ]]; then
    if [[ "$actual_status" != "0000000000000000" ]]; then
      printf "  %-32s FAIL status=0x%s\n" "$name" "$actual_status"
      return 1
    fi
    local actual_nibble_count_le; actual_nibble_count_le="$(dd if="$out_file" bs=1 skip=8 count=8 2>/dev/null | xxd -p | tr -d '\n')"
    local actual_nc; actual_nc="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$actual_nibble_count_le'))[0])")"
    local expected_nc; expected_nc="$(python3 -c "n = '$nibbles_csv'; print(len([x for x in n.split(',') if x.strip()]) if n else 0)")"
    if [[ "$actual_nc" != "$expected_nc" ]]; then
      printf "  %-32s FAIL nibble_count=%d expected=%d\n" "$name" "$actual_nc" "$expected_nc"
      return 1
    fi
    local actual_ref_len_le; actual_ref_len_le="$(dd if="$out_file" bs=1 skip=24 count=8 2>/dev/null | xxd -p | tr -d '\n')"
    local actual_rl; actual_rl="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$actual_ref_len_le'))[0])")"
    local expected_rl; expected_rl="$(python3 -c "print(len(bytes.fromhex('$ref_hex')))")"
    if [[ "$actual_rl" != "$expected_rl" ]]; then
      printf "  %-32s FAIL ref_len=%d expected=%d\n" "$name" "$actual_rl" "$expected_rl"
      return 1
    fi
    if [[ "$expected_nc" -gt 0 ]]; then
      local actual_nibbles; actual_nibbles="$(dd if="$out_file" bs=1 skip=32 count="$expected_nc" 2>/dev/null | xxd -p | tr -d '\n')"
      local expected_nibbles; expected_nibbles="$(python3 -c "nibs = [int(n) for n in '$nibbles_csv'.split(',') if n.strip()]; print(bytes(nibs).hex())")"
      if [[ "$actual_nibbles" != "$expected_nibbles" ]]; then
        printf "  %-32s FAIL nibble mismatch\n    expected: %s\n    actual:   %s\n" "$name" "$expected_nibbles" "$actual_nibbles"
        return 1
      fi
    fi
    printf "  %-32s OK   nibbles=%d ref_len=%d\n" "$name" "$expected_nc" "$expected_rl"
    return 0
  else
    if [[ "$actual_status" == "0000000000000000" ]]; then
      printf "  %-32s FAIL expected rejection got status=0\n" "$name"
      return 1
    fi
    printf "  %-32s OK   rejected (kind=%s)\n" "$name" "$kind"
    return 0
  fi
}

FAILED=0
# 32-byte hash references (typical)
HASH32="$(python3 -c "print('cc' * 32)")"
HASH32_BB="$(python3 -c "print('bb' * 32)")"
EMBED_SMALL="$(python3 -c "print('c102')")"

run_case "ext_short_path"    extension "1,2"          "$HASH32"     || FAILED=1
run_case "ext_even_path"     extension "1,2,3,4"      "$HASH32"     || FAILED=1
run_case "ext_long_path"     extension "$(python3 -c "print(','.join(str(i & 0xf) for i in range(64)))")" "$HASH32_BB" || FAILED=1
run_case "ext_embed_ref"     extension "5,6"          "$EMBED_SMALL" || FAILED=1
# Rejections
run_case "leaf_node"         leaf      "1,2"          "$HASH32"     || FAILED=1
run_case "branch_node"       branch    ""             ""            || FAILED=1
run_case "malformed_1item"   invalid   ""             ""            || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: mpt_extension_extract decodes extensions and rejects non-extensions"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
