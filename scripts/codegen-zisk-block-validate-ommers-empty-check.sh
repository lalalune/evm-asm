#!/usr/bin/env bash
# codegen-zisk-block-validate-ommers-empty-check.sh -- PR-K84.
#
# Verify post-merge invariant: block.body.ommers == [] (= 0xc0).
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

echo "==> emit zisk_block_validate_ommers_empty ELF"
lake exe codegen --program zisk_block_validate_ommers_empty --halt linux93 \
  -o gen-out/zisk_block_validate_ommers_empty

REPO_ROOT="$(pwd)"

# run_case <name> <expected_status> <ommers_json>
run_case() {
  local name="$1" expected_status="$2" ommers="$3"

  local in_file="$REPO_ROOT/gen-out/zisk_block_validate_ommers_empty_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_block_validate_ommers_empty_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import json, struct, sys
import rlp

ommers_raw = json.loads('''$ommers''')
# Convert hex strings → bytes; nested lists recurse.
def conv(x):
    if isinstance(x, str):
        return bytes.fromhex(x)
    if isinstance(x, list):
        return [conv(e) for e in x]
    return x

# Build block body: [txs (empty), ommers (variable), wds (empty)]
body = [[], conv(ommers_raw), []]
body_rlp = rlp.encode(body)
with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(body_rlp)))
    f.write(body_rlp)
    pad = (-(8 + len(body_rlp))) % 8
    if pad:
        f.write(b'\x00' * pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_block_validate_ommers_empty.elf \
    -i "$in_file" -o "$out_file" -n 500000 \
    >"$REPO_ROOT/gen-out/zisk_block_validate_ommers_empty_${name}.emu.log" 2>&1 || true

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

# A minimal "uncle" — just a stub list of empty fields. Not RLP-valid
# as a full header, but valid as an RLP item.
FAKE_OMMER='[]'

FAILED=0
# Post-merge canonical: empty ommers
run_case "empty_ommers"      0 "[]"                       || FAILED=1

# Single uncle (pre-merge) → reject
run_case "one_uncle"         1 "[$FAKE_OMMER]"            || FAILED=1

# Two uncles → reject
run_case "two_uncles"        1 "[$FAKE_OMMER, $FAKE_OMMER]" || FAILED=1

# Non-list body → parse fail
NON_LIST_FILE="$REPO_ROOT/gen-out/zisk_block_validate_ommers_empty_non_list.input"
python3 -c "
import struct, sys
b = bytes([0x80])
with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(b)))
    f.write(b)
    f.write(b'\x00' * 7)
" "$NON_LIST_FILE"
"$ZISKEMU" -e gen-out/zisk_block_validate_ommers_empty.elf \
  -i "$NON_LIST_FILE" -o "$REPO_ROOT/gen-out/zisk_block_validate_ommers_empty_non_list.output" \
  -n 500000 >"$REPO_ROOT/gen-out/zisk_block_validate_ommers_empty_non_list.emu.log" 2>&1 || true
NL_STATUS="$(xxd -p -l 8 "$REPO_ROOT/gen-out/zisk_block_validate_ommers_empty_non_list.output" | tr -d '\n')"
if [[ "$NL_STATUS" == "0200000000000000" ]]; then
  printf "  %-30s OK   status=2 (parse fail)\n" "non_list_parse_fail"
else
  printf "  %-30s FAIL  status=0x%s\n" "non_list_parse_fail" "$NL_STATUS"
  FAILED=1
fi

# 2-field body (missing withdrawals) — parse fail on field 2 lookup
TWO_FIELD_FILE="$REPO_ROOT/gen-out/zisk_block_validate_ommers_empty_two_field.input"
uv run --directory execution-specs --quiet python3 -c "
import struct, sys, rlp
body = [[], []]
body_rlp = rlp.encode(body)
with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(body_rlp)))
    f.write(body_rlp)
    pad = (-(8 + len(body_rlp))) % 8
    if pad:
        f.write(b'\x00' * pad)
" "$TWO_FIELD_FILE"
"$ZISKEMU" -e gen-out/zisk_block_validate_ommers_empty.elf \
  -i "$TWO_FIELD_FILE" -o "$REPO_ROOT/gen-out/zisk_block_validate_ommers_empty_two_field.output" \
  -n 500000 >"$REPO_ROOT/gen-out/zisk_block_validate_ommers_empty_two_field.emu.log" 2>&1 || true
TF_STATUS="$(xxd -p -l 8 "$REPO_ROOT/gen-out/zisk_block_validate_ommers_empty_two_field.output" | tr -d '\n')"
if [[ "$TF_STATUS" == "0200000000000000" ]]; then
  printf "  %-30s OK   status=2 (no withdrawals → parse fail)\n" "two_field_pre_shanghai"
else
  printf "  %-30s FAIL  status=0x%s\n" "two_field_pre_shanghai" "$TF_STATUS"
  FAILED=1
fi

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: block_validate_ommers_empty enforces post-merge empty-ommers invariant"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
