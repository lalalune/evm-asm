#!/usr/bin/env bash
# codegen-zisk-block-validate-empty-receipts-root-check.sh -- PR-K181.
#
# Verify header.field[5] (receipts_root) == EMPTY_TRIE_ROOT.
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

echo "==> emit zisk_block_validate_empty_receipts_root ELF"
lake exe codegen --program zisk_block_validate_empty_receipts_root --halt linux93 \
  -o gen-out/zisk_block_validate_empty_receipts_root

REPO_ROOT="$(pwd)"

EMPTY_TRIE_ROOT="56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421"

# run_case <name> <receipts_root_hex_or_special> <exp_status> <exp_valid>
run_case() {
  local name="$1" rr="$2" exp_status="$3" exp_valid="$4"

  local in_file="$REPO_ROOT/gen-out/zisk_block_validate_empty_receipts_root_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_block_validate_empty_receipts_root_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys, rlp
rr = '$rr'
if rr == 'garbage':
    header_rlp = b'\\x00'
else:
    if rr == 'short':
        field5 = b'\\xaa'*16
    else:
        field5 = bytes.fromhex(rr)
    fields = [
        b'\\x11'*32, b'\\x22'*32, b'\\x33'*20, b'\\x44'*32, b'\\x55'*32,
        field5, b'\\x00'*256, b'', b'\\x01', b'\\x83\\xff\\xff\\xff',
        b'', b'\\x83\\x01\\x02\\x03', b'', b'\\x77'*32, b'\\x00'*8,
    ]
    header_rlp = rlp.encode(fields)
with open(sys.argv[1], 'wb') as f:
    record = struct.pack('<Q', len(header_rlp)) + header_rlp
    f.write(record)
    pad = (-len(record)) % 8
    if pad: f.write(b'\x00' * pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_block_validate_empty_receipts_root.elf \
    -i "$in_file" -o "$out_file" -n 1000000 \
    >"$REPO_ROOT/gen-out/zisk_block_validate_empty_receipts_root_${name}.emu.log" 2>&1 || true

  local status_le; status_le="$(xxd -p -l 8 "$out_file" | tr -d '\n')"
  local valid_le;  valid_le="$( dd if="$out_file" bs=1 skip=8 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local status valid
  status="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$status_le'))[0])")"
  valid="$( python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$valid_le'))[0])")"

  if [[ "$status" == "$exp_status" && "$valid" == "$exp_valid" ]]; then
    printf "  %-28s OK   status=%s valid=%s\n" "$name" "$status" "$valid"
    return 0
  else
    printf "  %-28s FAIL status=%s/exp%s valid=%s/exp%s\n" \
      "$name" "$status" "$exp_status" "$valid" "$exp_valid"
    return 1
  fi
}

FAILED=0
run_case "match_empty"        "$EMPTY_TRIE_ROOT"                                              0 1 || FAILED=1
run_case "mismatch_ff"        "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff" 0 0 || FAILED=1
run_case "mismatch_zero"      "0000000000000000000000000000000000000000000000000000000000000000" 0 0 || FAILED=1
run_case "fail_short_field"   "short"                                                            2 0 || FAILED=1
run_case "fail_garbage"       "garbage"                                                          1 0 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: block_validate_empty_receipts_root accepts EMPTY_TRIE_ROOT and rejects others"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
