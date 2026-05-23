#!/usr/bin/env bash
# codegen-zisk-account-extract-storage-root-check.sh -- PR-K119.
#
# Extract field 2 (storage_root, 32 B) of an account RLP.
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

echo "==> emit zisk_account_extract_storage_root ELF"
lake exe codegen --program zisk_account_extract_storage_root --halt linux93 \
  -o gen-out/zisk_account_extract_storage_root

REPO_ROOT="$(pwd)"

# run_case <name> <kind> <storage_root_hex> <expected_status>
run_case() {
  local name="$1" kind="$2" storage_root="$3" exp_status="${4:-0}"

  local in_file="$REPO_ROOT/gen-out/zisk_account_extract_storage_root_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_account_extract_storage_root_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys, rlp
kind = '$kind'
storage_root = bytes.fromhex('$storage_root') if '$storage_root' else b''

if kind == 'account':
    account = [0, 10**18, storage_root, bytes([0x55]*32)]
elif kind == 'eoa_empty_trie':
    EMPTY_TRIE_ROOT = bytes.fromhex('56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421')
    account = [0, 0, EMPTY_TRIE_ROOT, bytes.fromhex('c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470')]
elif kind == 'bad_field2_short':
    account = [0, 0, bytes([0x11]*16), bytes([0x22]*32)]
elif kind == 'three_items':
    account = [0, 0, bytes([0x11]*32)]
else:
    raise ValueError(kind)

account_rlp = rlp.encode(account)
with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(account_rlp)))
    f.write(account_rlp)
    pad = (-(8 + len(account_rlp))) % 8
    if pad: f.write(b'\x00' * pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_account_extract_storage_root.elf \
    -i "$in_file" -o "$out_file" -n 1000000 \
    >"$REPO_ROOT/gen-out/zisk_account_extract_storage_root_${name}.emu.log" 2>&1 || true

  local actual_status; actual_status="$(xxd -p -l 8 "$out_file" | tr -d '\n')"
  local exp_status_le; exp_status_le="$(python3 -c "print(int('$exp_status').to_bytes(8, 'little').hex())")"

  if [[ "$actual_status" != "$exp_status_le" ]]; then
    printf "  %-32s FAIL status=0x%s expected=%d\n" "$name" "$actual_status" "$exp_status"
    return 1
  fi
  if [[ "$exp_status" != "0" ]]; then
    printf "  %-32s OK   status=%d (rejected)\n" "$name" "$exp_status"
    return 0
  fi
  local actual_root; actual_root="$(dd if="$out_file" bs=1 skip=8 count=32 2>/dev/null | xxd -p | tr -d '\n')"
  if [[ "$actual_root" == "$storage_root" ]]; then
    printf "  %-32s OK   root=%s..\n" "$name" "${actual_root:0:16}"
    return 0
  else
    printf "  %-32s FAIL\n    expected: %s\n    actual:   %s\n" "$name" "$storage_root" "$actual_root"
    return 1
  fi
}

FAILED=0
EMPTY_TRIE_ROOT="56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421"
ROOT_DEAD="$(python3 -c "print('de' * 32)")"
ROOT_BEEF="$(python3 -c "print('be' * 32)")"

run_case "empty_trie"          account            "$EMPTY_TRIE_ROOT"        || FAILED=1
run_case "eoa_canonical"       eoa_empty_trie     "$EMPTY_TRIE_ROOT"        || FAILED=1
run_case "contract_dead"       account            "$ROOT_DEAD"              || FAILED=1
run_case "contract_beef"       account            "$ROOT_BEEF"              || FAILED=1
# Rejections
run_case "field2_short_16B"    bad_field2_short   ""              2 || FAILED=1
run_case "three_item_field2"   three_items        "1111111111111111111111111111111111111111111111111111111111111111" 0 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: account_extract_storage_root returns field 2"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
