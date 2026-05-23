#!/usr/bin/env bash
# codegen-zisk-account-storage-root-is-empty-check.sh -- PR-K133.
#
# Predicate: storage_root == EMPTY_TRIE_ROOT?
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

echo "==> emit zisk_account_storage_root_is_empty ELF"
lake exe codegen --program zisk_account_storage_root_is_empty --halt linux93 \
  -o gen-out/zisk_account_storage_root_is_empty

REPO_ROOT="$(pwd)"

# run_case <name> <storage_root_hex> <expected_is_empty>
run_case() {
  local name="$1" sr="$2" exp_empty="$3"

  local in_file="$REPO_ROOT/gen-out/zisk_account_storage_root_is_empty_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_account_storage_root_is_empty_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys, rlp
sr = bytes.fromhex('$sr')
account = [42, 10**18, sr, bytes([0xab]*32)]
account_rlp = rlp.encode(account)
with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(account_rlp)))
    f.write(account_rlp)
    pad = (-(8 + len(account_rlp))) % 8
    if pad: f.write(b'\x00' * pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_account_storage_root_is_empty.elf \
    -i "$in_file" -o "$out_file" -n 1000000 \
    >"$REPO_ROOT/gen-out/zisk_account_storage_root_is_empty_${name}.emu.log" 2>&1 || true

  local actual_status; actual_status="$(xxd -p -l 8 "$out_file" | tr -d '\n')"
  local actual_empty_le; actual_empty_le="$(dd if="$out_file" bs=1 skip=8 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local actual_empty; actual_empty="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$actual_empty_le'))[0])")"

  if [[ "$actual_status" == "0000000000000000" && "$actual_empty" == "$exp_empty" ]]; then
    printf "  %-32s OK   is_empty=%d\n" "$name" "$exp_empty"
    return 0
  else
    printf "  %-32s FAIL status=0x%s is_empty=%d expected=%d\n" "$name" "$actual_status" "$actual_empty" "$exp_empty"
    return 1
  fi
}

ETR="56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421"
ZEROS="$(python3 -c "print('00' * 32)")"
ONES="$(python3 -c "print('ff' * 32)")"
NEAR_ETR="56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b422"

FAILED=0
run_case "canonical_empty_trie"    "$ETR"      1 || FAILED=1
run_case "all_zeros"               "$ZEROS"    0 || FAILED=1
run_case "all_ones"                "$ONES"     0 || FAILED=1
run_case "near_etr_last_byte"      "$NEAR_ETR" 0 || FAILED=1
run_case "random_root"             "$(python3 -c "print('ab' * 32)")" 0 || FAILED=1
# Boundary: only first byte differs
NEAR_ETR_FIRST="57e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421"
run_case "near_etr_first_byte"     "$NEAR_ETR_FIRST" 0 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: account_storage_root_is_empty matches storage_root == EMPTY_TRIE_ROOT"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
