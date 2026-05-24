#!/usr/bin/env bash
# codegen-zisk-block-validate-empty-block-check.sh -- PR-K182.
#
# Validate that a block is completely empty post-merge: 4 root
# fields equal their canonical empty constants, and the body has
# 3 empty fields.
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

echo "==> emit zisk_block_validate_empty_block ELF"
lake exe codegen --program zisk_block_validate_empty_block --halt linux93 \
  -o gen-out/zisk_block_validate_empty_block

REPO_ROOT="$(pwd)"

EMPTY_TRIE_ROOT="56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421"
EMPTY_OMMERS_HASH="1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347"

# run_case <name> <break: 'none' | 'tx_root' | 'ommers_hash' | 'rcpts_root' |
#                          'wdraws_root' | 'tx_body' | 'ommers_body' |
#                          'wdraws_body' >
#         <exp_status> <exp_valid>
run_case() {
  local name="$1" brk="$2" exp_status="$3" exp_valid="$4"

  local in_file="$REPO_ROOT/gen-out/zisk_block_validate_empty_block_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_block_validate_empty_block_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys, rlp
brk = '$brk'
EMPTY_TRIE_ROOT = bytes.fromhex('$EMPTY_TRIE_ROOT')
EMPTY_OMMERS_HASH = bytes.fromhex('$EMPTY_OMMERS_HASH')
BAD = b'\\xff'*32

ommers_hash      = BAD if brk == 'ommers_hash' else EMPTY_OMMERS_HASH
tx_root          = BAD if brk == 'tx_root'     else EMPTY_TRIE_ROOT
rcpts_root       = BAD if brk == 'rcpts_root'  else EMPTY_TRIE_ROOT
wdraws_root      = BAD if brk == 'wdraws_root' else EMPTY_TRIE_ROOT

fields = [
    b'\\x11'*32, ommers_hash, b'\\x33'*20, b'\\x44'*32, tx_root,
    rcpts_root, b'\\x00'*256, b'', b'\\x01', b'\\x83\\xff\\xff\\xff',
    b'', b'\\x83\\x01\\x02\\x03', b'', b'\\x77'*32, b'\\x00'*8,
    b'\\x82\\x12\\x34', wdraws_root,
]
header_rlp = rlp.encode(fields)

# Body: each field defaults empty, possibly broken
tx_body     = [b'\\xaa'*10] if brk == 'tx_body'     else []
ommers_body = [[]]            if brk == 'ommers_body' else []
wdraws_body = [[b'\\x01', b'\\x02', b'\\xee'*20, b'\\x03']] if brk == 'wdraws_body' else []
body_rlp = rlp.encode([tx_body, ommers_body, wdraws_body])

with open(sys.argv[1], 'wb') as f:
    record = struct.pack('<Q', len(header_rlp)) + \
             struct.pack('<Q', len(body_rlp)) + \
             header_rlp + body_rlp
    f.write(record)
    pad = (-len(record)) % 8
    if pad: f.write(b'\x00' * pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_block_validate_empty_block.elf \
    -i "$in_file" -o "$out_file" -n 2000000 \
    >"$REPO_ROOT/gen-out/zisk_block_validate_empty_block_${name}.emu.log" 2>&1 || true

  local status_le; status_le="$(xxd -p -l 8 "$out_file" | tr -d '\n')"
  local valid_le;  valid_le="$( dd if="$out_file" bs=1 skip=8 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local status valid
  status="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$status_le'))[0])")"
  valid="$( python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$valid_le'))[0])")"

  if [[ "$status" == "$exp_status" && "$valid" == "$exp_valid" ]]; then
    printf "  %-32s OK   status=%s valid=%s\n" "$name" "$status" "$valid"
    return 0
  else
    printf "  %-32s FAIL status=%s/exp%s valid=%s/exp%s\n" \
      "$name" "$status" "$exp_status" "$valid" "$exp_valid"
    return 1
  fi
}

FAILED=0
run_case "all_empty"              "none"        0 1 || FAILED=1
run_case "bad_tx_root"            "tx_root"     0 0 || FAILED=1
run_case "bad_ommers_hash"        "ommers_hash" 0 0 || FAILED=1
run_case "bad_rcpts_root"         "rcpts_root"  0 0 || FAILED=1
run_case "bad_wdraws_root"        "wdraws_root" 0 0 || FAILED=1
run_case "body_has_tx"            "tx_body"     0 0 || FAILED=1
run_case "body_has_ommers"        "ommers_body" 0 0 || FAILED=1
run_case "body_has_withdrawal"    "wdraws_body" 0 0 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: block_validate_empty_block enforces all 8 empty-block invariants"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
