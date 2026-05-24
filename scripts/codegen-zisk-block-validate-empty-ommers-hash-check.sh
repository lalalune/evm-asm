#!/usr/bin/env bash
# codegen-zisk-block-validate-empty-ommers-hash-check.sh -- PR-K179.
#
# Extract header.field[1] (ommers_hash) and check it equals the
# post-merge constant keccak256(rlp([])).
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

echo "==> emit zisk_block_validate_empty_ommers_hash ELF"
lake exe codegen --program zisk_block_validate_empty_ommers_hash --halt linux93 \
  -o gen-out/zisk_block_validate_empty_ommers_hash

REPO_ROOT="$(pwd)"

EMPTY_OMMERS_HASH="1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347"

# run_case <name> <ommers_hash_hex_or_'short'_or_'garbage'> <exp_status> <exp_valid>
run_case() {
  local name="$1" oh="$2" exp_status="$3" exp_valid="$4"

  local in_file="$REPO_ROOT/gen-out/zisk_block_validate_empty_ommers_hash_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_block_validate_empty_ommers_hash_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys, rlp
oh = '$oh'
fields = [
    b'\\x11'*32, None,                # field 1 = ommers_hash; placeholder
    b'\\x33'*20, b'\\x44'*32, b'\\x55'*32, b'\\x66'*32, b'\\x00'*256,
    b'', b'\\x01', b'\\x83\\xff\\xff\\xff', b'', b'\\x83\\x01\\x02\\x03',
    b'', b'\\x77'*32, b'\\x00'*8,
]
if oh == 'garbage':
    header_rlp = b'\\x00'
else:
    if oh == 'short':
        fields[1] = b'\\xaa'*16
    else:
        fields[1] = bytes.fromhex(oh)
    header_rlp = rlp.encode(fields)
with open(sys.argv[1], 'wb') as f:
    record = struct.pack('<Q', len(header_rlp)) + header_rlp
    f.write(record)
    pad = (-len(record)) % 8
    if pad: f.write(b'\x00' * pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_block_validate_empty_ommers_hash.elf \
    -i "$in_file" -o "$out_file" -n 1000000 \
    >"$REPO_ROOT/gen-out/zisk_block_validate_empty_ommers_hash_${name}.emu.log" 2>&1 || true

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
run_case "match_empty_ommers"     "$EMPTY_OMMERS_HASH"                                              0 1 || FAILED=1
run_case "mismatch_nonempty_hash" "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff" 0 0 || FAILED=1
run_case "mismatch_zero_hash"     "0000000000000000000000000000000000000000000000000000000000000000" 0 0 || FAILED=1
run_case "fail_short_field"       "short"                                                            2 0 || FAILED=1
run_case "fail_garbage_header"    "garbage"                                                          1 0 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: block_validate_empty_ommers_hash accepts the post-merge constant and rejects others"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
