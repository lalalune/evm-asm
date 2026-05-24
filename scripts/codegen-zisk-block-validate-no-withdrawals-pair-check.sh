#!/usr/bin/env bash
# codegen-zisk-block-validate-no-withdrawals-pair-check.sh -- PR-K180.
#
# Verify header.withdrawals_root == EMPTY_TRIE_ROOT AND
# body.field[2] == 0xc0 (empty withdrawals list).
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

echo "==> emit zisk_block_validate_no_withdrawals_pair ELF"
lake exe codegen --program zisk_block_validate_no_withdrawals_pair --halt linux93 \
  -o gen-out/zisk_block_validate_no_withdrawals_pair

REPO_ROOT="$(pwd)"

EMPTY_TRIE_ROOT="56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421"

# run_case <name> <header_wroot_hex_or_special> <body_withdrawal_count>
#                 <exp_status> <exp_valid>
run_case() {
  local name="$1" wroot="$2" wcount="$3" exp_status="$4" exp_valid="$5"

  local in_file="$REPO_ROOT/gen-out/zisk_block_validate_no_withdrawals_pair_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_block_validate_no_withdrawals_pair_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys, rlp
wroot = '$wroot'
wcount = $wcount

if wroot == 'short':
    field16 = b'\\xaa'*16
elif wroot == 'garbage':
    # We'll emit a malformed header below
    field16 = b'\\x00'*32
else:
    field16 = bytes.fromhex(wroot)

fields = [
    b'\\x11'*32, b'\\x22'*32, b'\\x33'*20, b'\\x44'*32, b'\\x55'*32,
    b'\\x66'*32, b'\\x00'*256, b'', b'\\x01', b'\\x83\\xff\\xff\\xff',
    b'', b'\\x83\\x01\\x02\\x03', b'', b'\\x77'*32, b'\\x00'*8,
    b'\\x82\\x12\\x34', field16,
]
if wroot == 'garbage':
    header_rlp = b'\\x00'
else:
    header_rlp = rlp.encode(fields)

withdrawals = []
for i in range(wcount):
    # Each withdrawal: [index, validator_index, address (20B), amount]
    withdrawals.append([i.to_bytes(2, 'big'), i.to_bytes(4, 'big'),
                        b'\\xee'*20, (i*1000).to_bytes(4, 'big')])
body_rlp = rlp.encode([[], [], withdrawals])

with open(sys.argv[1], 'wb') as f:
    record = struct.pack('<Q', len(header_rlp)) + \
             struct.pack('<Q', len(body_rlp)) + \
             header_rlp + body_rlp
    f.write(record)
    pad = (-len(record)) % 8
    if pad: f.write(b'\x00' * pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_block_validate_no_withdrawals_pair.elf \
    -i "$in_file" -o "$out_file" -n 1000000 \
    >"$REPO_ROOT/gen-out/zisk_block_validate_no_withdrawals_pair_${name}.emu.log" 2>&1 || true

  local status_le; status_le="$(xxd -p -l 8 "$out_file" | tr -d '\n')"
  local valid_le;  valid_le="$( dd if="$out_file" bs=1 skip=8 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local status valid
  status="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$status_le'))[0])")"
  valid="$( python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$valid_le'))[0])")"

  if [[ "$status" == "$exp_status" && "$valid" == "$exp_valid" ]]; then
    printf "  %-30s OK   status=%s valid=%s\n" "$name" "$status" "$valid"
    return 0
  else
    printf "  %-30s FAIL status=%s/exp%s valid=%s/exp%s\n" \
      "$name" "$status" "$exp_status" "$valid" "$exp_valid"
    return 1
  fi
}

FAILED=0
# Both sides agree: empty withdrawals
run_case "both_empty"           "$EMPTY_TRIE_ROOT" 0 0 1 || FAILED=1
# Header claims empty, body has withdrawals
run_case "body_has_withdrawals" "$EMPTY_TRIE_ROOT" 2 0 0 || FAILED=1
# Header has non-empty root, body empty
run_case "header_nonempty_root" "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff" 0 0 0 || FAILED=1
# Header has all-zero root, body empty
run_case "header_zero_root"     "0000000000000000000000000000000000000000000000000000000000000000" 0 0 0 || FAILED=1
# Header field 16 too short
run_case "header_size_fail"     "short"            0 3 0 || FAILED=1
# Header is garbage
run_case "header_parse_fail"    "garbage"          0 2 0 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: block_validate_no_withdrawals_pair enforces both sides"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
