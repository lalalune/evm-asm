#!/usr/bin/env bash
# codegen-zisk-rlp-list-truncate-to-n-fields-check.sh -- PR-K144.
#
# Truncate an RLP list to its first n fields and re-encode the
# outer list prefix.
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

echo "==> emit zisk_rlp_list_truncate_to_n_fields ELF"
lake exe codegen --program zisk_rlp_list_truncate_to_n_fields --halt linux93 \
  -o gen-out/zisk_rlp_list_truncate_to_n_fields

REPO_ROOT="$(pwd)"

# run_case <name> <fields_json> <n>
run_case() {
  local name="$1" fields="$2" n="$3"

  local in_file="$REPO_ROOT/gen-out/zisk_rlp_list_truncate_to_n_fields_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_rlp_list_truncate_to_n_fields_${name}.output"
  local exp_hex_file="$REPO_ROOT/gen-out/zisk_rlp_list_truncate_to_n_fields_${name}.expected.hex"

  uv run --directory execution-specs --quiet python3 -c "
import json, struct, sys, rlp
fields_raw = json.loads('''$fields''')
def conv(x):
    if isinstance(x, str) and x.startswith('hex:'): return bytes.fromhex(x[4:])
    if isinstance(x, list): return [conv(e) for e in x]
    return x
fields = [conv(f) for f in fields_raw]
n = $n
list_rlp = rlp.encode(fields)
with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(list_rlp)))
    f.write(struct.pack('<Q', n))
    f.write(list_rlp)
    pad = (-(16 + len(list_rlp))) % 8
    if pad: f.write(b'\x00' * pad)
expected = rlp.encode(fields[:n])
with open(sys.argv[2], 'w') as f:
    f.write(expected.hex())
" "$in_file" "$exp_hex_file"

  "$ZISKEMU" -e gen-out/zisk_rlp_list_truncate_to_n_fields.elf \
    -i "$in_file" -o "$out_file" -n 1000000 \
    >"$REPO_ROOT/gen-out/zisk_rlp_list_truncate_to_n_fields_${name}.emu.log" 2>&1 || true

  local actual_status; actual_status="$(xxd -p -l 8 "$out_file" | tr -d '\n')"
  local actual_len_le; actual_len_le="$(dd if="$out_file" bs=1 skip=8 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local actual_len; actual_len="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$actual_len_le'))[0])")"
  local expected_hex; expected_hex="$(cat "$exp_hex_file")"
  local expected_len; expected_len=$(( ${#expected_hex} / 2 ))
  local actual_hex; actual_hex="$(dd if="$out_file" bs=1 skip=16 count="$expected_len" 2>/dev/null | xxd -p | tr -d '\n')"

  if [[ "$actual_status" == "0000000000000000" \
       && "$actual_len" == "$expected_len" \
       && "$actual_hex" == "$expected_hex" ]]; then
    printf "  %-30s OK   n=%d len=%d\n" "$name" "$n" "$expected_len"
    return 0
  else
    printf "  %-30s FAIL status=0x%s actual_len=%d expected_len=%d\n" "$name" "$actual_status" "$actual_len" "$expected_len"
    printf "      actual:   %s\n" "${actual_hex:0:80}"
    printf "      expected: %s\n" "${expected_hex:0:80}"
    return 1
  fi
}

FAILED=0
# Standard legacy tx → drop (v, r, s): 9 fields → 6
run_case "legacy_9to6" \
  '[42, 1000000000, 21000, "hex:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", 1000000000000000000, "", 27, "hex:1111111111111111111111111111111111111111111111111111111111111111", "hex:2222222222222222222222222222222222222222222222222222222222222222"]' \
  6 || FAILED=1

# Same as above, n == full count → identity
run_case "legacy_9to9_identity" \
  '[42, 1000000000, 21000, "hex:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", 1000000000000000000, "", 27, "hex:1111111111111111111111111111111111111111111111111111111111111111", "hex:2222222222222222222222222222222222222222222222222222222222222222"]' \
  9 || FAILED=1

# n == 0 → empty list (just 0xc0)
run_case "empty_list_n0" '[1, 2, 3]' 0 || FAILED=1

# n == 1 → single-field list
run_case "single_field" '[1, 2, 3]' 1 || FAILED=1

# EIP-7702 authorization tuple: 6 fields → 3 (sig drop), payload short enough to be a short list
run_case "auth_6to3" \
  '[1, "hex:dededededededededededededededededededede", 0, 1, "hex:1111111111111111111111111111111111111111111111111111111111111111", "hex:2222222222222222222222222222222222222222222222222222222222222222"]' \
  3 || FAILED=1

# Regression: field 0 is empty bytes (RLP-canonical 0 → 0x80).
# This trips the "K20 offset is content-not-item" trap if `payload_start`
# is taken from `rlp_list_nth_item(0).offset` rather than parsed from the
# outer list prefix. Pre-fix output was off-by-one for the body slice.
run_case "field0_zero_short_str" \
  '[0, 1000000000, 21000, "hex:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", 1000000000000000000, "", 27, "hex:1111111111111111111111111111111111111111111111111111111111111111", "hex:2222222222222222222222222222222222222222222222222222222222222222"]' \
  6 || FAILED=1

# Regression: field 0 with multi-byte short-string prefix.
run_case "field0_short_str_5b" \
  '["hex:cafebabe00", 2, 3]' 2 || FAILED=1

# n > number of fields → status 2
in_too_few="$REPO_ROOT/gen-out/zisk_rlp_list_truncate_to_n_fields_too_few.input"
out_too_few="$REPO_ROOT/gen-out/zisk_rlp_list_truncate_to_n_fields_too_few.output"
uv run --directory execution-specs --quiet python3 -c "
import struct, rlp
list_rlp = rlp.encode([1, 2, 3])
with open('$in_too_few', 'wb') as f:
    f.write(struct.pack('<Q', len(list_rlp)))
    f.write(struct.pack('<Q', 5))   # ask for 5 fields, only 3 exist
    f.write(list_rlp)
    pad = (-(16 + len(list_rlp))) % 8
    if pad: f.write(b'\x00' * pad)
"
"$ZISKEMU" -e gen-out/zisk_rlp_list_truncate_to_n_fields.elf \
  -i "$in_too_few" -o "$out_too_few" -n 1000000 \
  >"$REPO_ROOT/gen-out/zisk_rlp_list_truncate_to_n_fields_too_few.emu.log" 2>&1 || true
status_le="$(xxd -p -l 8 "$out_too_few" | tr -d '\n')"
exp_status_le="$(python3 -c "print(int(2).to_bytes(8, 'little').hex())")"
if [[ "$status_le" == "$exp_status_le" ]]; then
  printf "  %-30s OK   status=2 (rejected too few fields)\n" "too_few_fields"
else
  printf "  %-30s FAIL status=0x%s expected=0x%s\n" "too_few_fields" "$status_le" "$exp_status_le"
  FAILED=1
fi

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: rlp_list_truncate_to_n_fields re-encodes correctly"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
