#!/usr/bin/env bash
# codegen-zisk-header-validate-post-merge-check.sh -- PR-K67.
#
# Verify three post-merge header invariants:
#   1. ommers_hash == EMPTY_OMMERS_HASH
#   2. difficulty == 0
#   3. nonce == 8 zero bytes
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

echo "==> emit zisk_header_validate_post_merge ELF"
lake exe codegen --program zisk_header_validate_post_merge --halt linux93 \
  -o gen-out/zisk_header_validate_post_merge

REPO_ROOT="$(pwd)"

EMPTY_OMMERS_HASH="1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347"
ZERO_NONCE="0000000000000000"

# build_header writes a 15-field header RLP with overridable fields.
build_header() {
  local ommers_hash_hex="$1" difficulty="$2" nonce_hex="$3"
  uv run --directory execution-specs --quiet python3 -c "
import sys
import rlp
ommers_hash = bytes.fromhex('$ommers_hash_hex')
nonce = bytes.fromhex('$nonce_hex')
fields = [
    b'\x11' * 32,       # 0: parent_hash
    ommers_hash,        # 1: ommers_hash
    b'\x33' * 20,       # 2: coinbase
    b'\x44' * 32,       # 3: state_root
    b'\x55' * 32,       # 4: transactions_root
    b'\x66' * 32,       # 5: receipts_root
    b'\x00' * 256,      # 6: bloom
    $difficulty,        # 7: difficulty
    100,                # 8: number
    0x1c9c380,          # 9: gas_limit
    0x100,              # 10: gas_used
    1700000000,         # 11: timestamp
    b'test',            # 12: extra_data
    b'\x77' * 32,       # 13: prev_randao
    nonce,              # 14: nonce
]
sys.stdout.buffer.write(rlp.encode(fields))
"
}

# run_case <name> <expected_status> <ommers_hash> <difficulty> <nonce_hex>
run_case() {
  local name="$1" expected_status="$2" ommers="$3" diff="$4" nonce="$5"

  local header_file="$REPO_ROOT/gen-out/zisk_header_validate_post_merge_${name}.header"
  local in_file="$REPO_ROOT/gen-out/zisk_header_validate_post_merge_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_header_validate_post_merge_${name}.output"

  build_header "$ommers" "$diff" "$nonce" > "$header_file"
  python3 -c "
import struct, sys
with open(sys.argv[1], 'rb') as f:
    body = f.read()
out  = struct.pack('<Q', len(body))
out += body
pad = (-(8 + len(body))) % 8
if pad:
    out += b'\x00' * pad
sys.stdout.buffer.write(out)
" "$header_file" > "$in_file"

  "$ZISKEMU" -e gen-out/zisk_header_validate_post_merge.elf \
    -i "$in_file" -o "$out_file" -n 500000 \
    >"$REPO_ROOT/gen-out/zisk_header_validate_post_merge_${name}.emu.log" 2>&1 || true

  local actual; actual="$(xxd -p -l 8 "$out_file" | tr -d '\n')"
  local exp_le; exp_le="$(python3 -c "print(int('$expected_status').to_bytes(8, 'little').hex())")"

  if [[ "$actual" == "$exp_le" ]]; then
    printf "  %-30s OK   status=%d\n" "$name" "$expected_status"
    return 0
  else
    printf "  %-30s FAIL  expected status=%d got 0x%s\n" "$name" "$expected_status" "$actual"
    return 1
  fi
}

FAILED=0
# Pass: all three invariants hold
run_case "post_merge_canonical"     0 "$EMPTY_OMMERS_HASH" 0 "$ZERO_NONCE" || FAILED=1
# Fail 1: ommers_hash mismatch
run_case "ommers_mismatch_zero"     1 "0000000000000000000000000000000000000000000000000000000000000000" 0 "$ZERO_NONCE" || FAILED=1
run_case "ommers_mismatch_pattern"  1 "aabbccddeeff00112233445566778899aabbccddeeff00112233445566778899" 0 "$ZERO_NONCE" || FAILED=1
# Fail 2: difficulty != 0
run_case "diff_nonzero_small"       2 "$EMPTY_OMMERS_HASH" 1 "$ZERO_NONCE" || FAILED=1
run_case "diff_nonzero_large"       2 "$EMPTY_OMMERS_HASH" 1000000 "$ZERO_NONCE" || FAILED=1
# Fail 3: nonce not zero
run_case "nonce_lsb_set"            3 "$EMPTY_OMMERS_HASH" 0 "0000000000000001" || FAILED=1
run_case "nonce_msb_set"            3 "$EMPTY_OMMERS_HASH" 0 "0100000000000000" || FAILED=1
run_case "nonce_random"             3 "$EMPTY_OMMERS_HASH" 0 "deadbeefcafebabe" || FAILED=1
# Compound failures (asm should report whichever check fires first)
# Check order: ommers → difficulty → nonce
run_case "ommers_and_diff_fail"     1 "0000000000000000000000000000000000000000000000000000000000000000" 5 "$ZERO_NONCE" || FAILED=1
run_case "diff_and_nonce_fail"      2 "$EMPTY_OMMERS_HASH" 5 "deadbeefcafebabe" || FAILED=1

# Fail 4: non-list input
NON_LIST_FILE="$REPO_ROOT/gen-out/zisk_header_validate_post_merge_non_list.input"
python3 -c "
import struct, sys
b = bytes([0x80])
with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(b)))
    f.write(b)
    f.write(b'\x00' * 7)
" "$NON_LIST_FILE"
"$ZISKEMU" -e gen-out/zisk_header_validate_post_merge.elf \
  -i "$NON_LIST_FILE" -o "$REPO_ROOT/gen-out/zisk_header_validate_post_merge_non_list.output" \
  -n 500000 >"$REPO_ROOT/gen-out/zisk_header_validate_post_merge_non_list.emu.log" 2>&1 || true
NL_STATUS="$(xxd -p -l 8 "$REPO_ROOT/gen-out/zisk_header_validate_post_merge_non_list.output" | tr -d '\n')"
if [[ "$NL_STATUS" == "0400000000000000" ]]; then
  printf "  %-30s OK   status=4 (parse fail)\n" "non_list_parse_fail"
else
  printf "  %-30s FAIL  status=0x%s\n" "non_list_parse_fail" "$NL_STATUS"
  FAILED=1
fi

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: header_validate_post_merge enforces ommers_hash + difficulty + nonce invariants"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
