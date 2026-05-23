#!/usr/bin/env bash
# codegen-zisk-mpt-branch-node-encode-check.sh -- PR-K165.
#
# Wrap a pre-concatenated 17-slot payload into the branch-node RLP.
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

echo "==> emit zisk_mpt_branch_node_encode ELF"
lake exe codegen --program zisk_mpt_branch_node_encode --halt linux93 \
  -o gen-out/zisk_mpt_branch_node_encode

REPO_ROOT="$(pwd)"

# run_case <name> <slots_json>
# slots_json: JSON list of 17 hex strings (each is the RLP-encoded slot,
# already including any RLP prefix bytes -- e.g. "80" for empty, the
# 33-byte "a0..." string for hashed children, or the inline RLP for
# small children).
run_case() {
  local name="$1" slots="$2"

  local in_file="$REPO_ROOT/gen-out/zisk_mpt_branch_node_encode_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_mpt_branch_node_encode_${name}.output"
  local exp_hex_file="$REPO_ROOT/gen-out/zisk_mpt_branch_node_encode_${name}.expected.hex"

  uv run --directory execution-specs --quiet python3 -c "
import json, struct, sys
slots = json.loads('''$slots''')
assert len(slots) == 17, f'expected 17 slots, got {len(slots)}'
payload = b''.join(bytes.fromhex(s) for s in slots)

n = len(payload)
if n < 56:
    prefix = bytes([0xc0 + n])
else:
    n_bytes = n.to_bytes((n.bit_length() + 7) // 8, 'big')
    prefix = bytes([0xf7 + len(n_bytes)]) + n_bytes
expected = prefix + payload

with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', n))
    f.write(payload)
    pad = (-(8 + n)) % 8
    if pad: f.write(b'\x00' * pad)
with open(sys.argv[2], 'w') as f:
    f.write(expected.hex())
" "$in_file" "$exp_hex_file"

  "$ZISKEMU" -e gen-out/zisk_mpt_branch_node_encode.elf \
    -i "$in_file" -o "$out_file" -n 1000000 \
    >"$REPO_ROOT/gen-out/zisk_mpt_branch_node_encode_${name}.emu.log" 2>&1 || true

  local actual_status; actual_status="$(xxd -p -l 8 "$out_file" | tr -d '\n')"
  local actual_len_le; actual_len_le="$(dd if="$out_file" bs=1 skip=8 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local actual_len; actual_len="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$actual_len_le'))[0])")"
  local expected_hex; expected_hex="$(cat "$exp_hex_file")"
  local expected_len; expected_len=$(( ${#expected_hex} / 2 ))
  local cmp_len=$expected_len
  if [[ $cmp_len -gt 240 ]]; then cmp_len=240; fi
  local actual_hex; actual_hex="$(dd if="$out_file" bs=1 skip=16 count="$cmp_len" 2>/dev/null | xxd -p | tr -d '\n')"
  local expected_prefix="${expected_hex:0:$((2 * cmp_len))}"

  if [[ "$actual_status" == "0000000000000000" \
       && "$actual_len" == "$expected_len" \
       && "$actual_hex" == "$expected_prefix" ]]; then
    printf "  %-30s OK   len=%d\n" "$name" "$expected_len"
    return 0
  else
    printf "  %-30s FAIL status=0x%s actual_len=%d expected_len=%d\n" "$name" "$actual_status" "$actual_len" "$expected_len"
    printf "      actual:   %s...\n" "${actual_hex:0:80}"
    printf "      expected: %s...\n" "${expected_prefix:0:80}"
    return 1
  fi
}

HASH32="a0a1a2a3a4a5a6a7a8a9aaabacadaeafb0b1b2b3b4b5b6b7b8b9babbbcbdbebf"
HASHED_SLOT="\"a0$HASH32\""
EMPTY_SLOT='"80"'

FAILED=0
# All-empty branch (all 17 slots = 0x80)
SLOTS_ALL_EMPTY="$(python3 -c "import json; print(json.dumps(['80']*17))")"
run_case "all_empty"             "$SLOTS_ALL_EMPTY" || FAILED=1

# Single hashed child at slot 0, rest empty
python3 -c "
import json
slots = ['80']*17
slots[0] = 'a0' + '$HASH32'
print(json.dumps(slots))
" > /tmp/mbne_slots_one.json
run_case "one_hashed_slot0"      "$(cat /tmp/mbne_slots_one.json)" || FAILED=1

# Two hashed children at slot 0 and 8 (the rlp(0)/rlp(1) divergence shape)
python3 -c "
import json
slots = ['80']*17
slots[0] = 'a0' + '$HASH32'
slots[8] = 'a0' + 'b0b1b2b3b4b5b6b7b8b9babbbcbdbebfc0c1c2c3c4c5c6c7c8c9cacbcccdcecf'
print(json.dumps(slots))
" > /tmp/mbne_slots_two.json
run_case "two_hashed_slots"      "$(cat /tmp/mbne_slots_two.json)" || FAILED=1

# All-hashed (all 16 children + value)
python3 -c "
import json
slots = ['a0' + bytes([i] * 32).hex() for i in range(17)]
print(json.dumps(slots))
" > /tmp/mbne_slots_all_hashed.json
run_case "all_hashed"            "$(cat /tmp/mbne_slots_all_hashed.json)" || FAILED=1

# Inline child mix (some inline, some hashed, some empty)
python3 -c "
import json
slots = ['80']*17
slots[3] = 'c4820080'             # short inline list
slots[5] = 'a0' + '11'*32          # hashed
slots[15] = '85deadbeef00'         # short inline string
slots[16] = '80'                   # value empty
print(json.dumps(slots))
" > /tmp/mbne_slots_mixed.json
run_case "inline_hashed_mixed"   "$(cat /tmp/mbne_slots_mixed.json)" || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: mpt_branch_node_encode wraps the 17-slot payload with correct outer prefix"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
