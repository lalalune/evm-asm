#!/usr/bin/env bash
# codegen-zisk-header-root-is-empty-trie-check.sh -- PR-K161.
#
# Predicate: does header.field[i] equal EMPTY_TRIE_ROOT?
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

echo "==> emit zisk_header_root_is_empty_trie ELF"
lake exe codegen --program zisk_header_root_is_empty_trie --halt linux93 \
  -o gen-out/zisk_header_root_is_empty_trie

REPO_ROOT="$(pwd)"

# run_case <name> <field_idx> <field_value_hex> <expected_is_equal>
run_case() {
  local name="$1" idx="$2" value="$3" exp="$4"

  local in_file="$REPO_ROOT/gen-out/zisk_header_root_is_empty_trie_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_header_root_is_empty_trie_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys, rlp
idx = $idx
value_bytes = bytes.fromhex('$value')

H32 = bytes([0xaa] * 32)
ADDR = bytes([0xbb] * 20)
EMPTY_TRIE_ROOT = bytes.fromhex(
    '56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421')
# Default cancun-style 20-field header.
hdr = [H32, H32, ADDR, H32, EMPTY_TRIE_ROOT, EMPTY_TRIE_ROOT,
       b'\\x00' * 256, 0, 1, 30000000, 21000, 1700000000,
       b'', H32, b'\\x00'*8, 10**9, EMPTY_TRIE_ROOT,
       131072, 786432, H32]
hdr[idx] = value_bytes
header_rlp = rlp.encode(hdr)

with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(header_rlp)))
    f.write(struct.pack('<Q', idx))
    f.write(header_rlp)
    pad = (-(16 + len(header_rlp))) % 8
    if pad: f.write(b'\x00' * pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_header_root_is_empty_trie.elf \
    -i "$in_file" -o "$out_file" -n 100000 \
    >"$REPO_ROOT/gen-out/zisk_header_root_is_empty_trie_${name}.emu.log" 2>&1 || true

  local actual_status; actual_status="$(xxd -p -l 8 "$out_file" | tr -d '\n')"
  local actual_eq_le; actual_eq_le="$(dd if="$out_file" bs=1 skip=8 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local actual_eq; actual_eq="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$actual_eq_le'))[0])")"

  if [[ "$actual_status" == "0000000000000000" && "$actual_eq" == "$exp" ]]; then
    printf "  %-30s OK   idx=%d is_empty=%d\n" "$name" "$idx" "$exp"
    return 0
  else
    printf "  %-30s FAIL status=0x%s is_empty=%d expected=%d\n" "$name" "$actual_status" "$actual_eq" "$exp"
    return 1
  fi
}

ETR="56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421"
OTHER="aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
# Single-byte difference (last byte flipped).
ETR_FLIP="56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b420"
# Single-byte difference (first byte flipped).
ETR_FLIP_HI="57e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421"

FAILED=0
# field 4 (transactions_root) at EMPTY_TRIE_ROOT
run_case "tx_root_empty"          4 "$ETR"          1 || FAILED=1
# field 5 (receipts_root) at EMPTY_TRIE_ROOT
run_case "receipts_root_empty"    5 "$ETR"          1 || FAILED=1
# field 16 (withdrawals_root) at EMPTY_TRIE_ROOT
run_case "withdrawals_root_empty" 16 "$ETR"         1 || FAILED=1
# Not-empty (random hash)
run_case "tx_root_other"          4 "$OTHER"        0 || FAILED=1
# Off-by-one tail
run_case "etr_tail_diff"          4 "$ETR_FLIP"     0 || FAILED=1
# Off-by-one head
run_case "etr_head_diff"          4 "$ETR_FLIP_HI"  0 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: header_root_is_empty_trie detects EMPTY_TRIE_ROOT at any field index"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
