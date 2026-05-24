#!/usr/bin/env bash
# codegen-zisk-mpt-branch-payload-two-slots-check.sh -- PR-K167.
#
# Produce the 17-slot payload bytes for a branch node with two
# active slots (rest empty).
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

echo "==> emit zisk_mpt_branch_payload_two_slots ELF"
lake exe codegen --program zisk_mpt_branch_payload_two_slots --halt linux93 \
  -o gen-out/zisk_mpt_branch_payload_two_slots

REPO_ROOT="$(pwd)"

# run_case <name> <idx_a> <bytes_a_hex> <idx_b> <bytes_b_hex> <expected_status>
run_case() {
  local name="$1" idx_a="$2" bytes_a="$3" idx_b="$4" bytes_b="$5" exp_status="$6"

  local in_file="$REPO_ROOT/gen-out/zisk_mpt_branch_payload_two_slots_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_mpt_branch_payload_two_slots_${name}.output"
  local exp_hex_file="$REPO_ROOT/gen-out/zisk_mpt_branch_payload_two_slots_${name}.expected.hex"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys
idx_a = $idx_a
idx_b = $idx_b
bytes_a = bytes.fromhex('$bytes_a')
bytes_b = bytes.fromhex('$bytes_b')

slots = [b'\\x80'] * 17
expected_status = $exp_status
if expected_status == 0:
    slots[idx_a] = bytes_a
    slots[idx_b] = bytes_b
expected_payload = b''.join(slots)

with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', idx_a))
    f.write(struct.pack('<Q', len(bytes_a)))
    f.write(struct.pack('<Q', idx_b))
    f.write(struct.pack('<Q', len(bytes_b)))
    f.write(bytes_a)
    f.write(bytes_b)
    pad = (-(32 + len(bytes_a) + len(bytes_b))) % 8
    if pad: f.write(b'\x00' * pad)
with open(sys.argv[2], 'w') as f:
    f.write(expected_payload.hex())
" "$in_file" "$exp_hex_file"

  "$ZISKEMU" -e gen-out/zisk_mpt_branch_payload_two_slots.elf \
    -i "$in_file" -o "$out_file" -n 1000000 \
    >"$REPO_ROOT/gen-out/zisk_mpt_branch_payload_two_slots_${name}.emu.log" 2>&1 || true

  local actual_status; actual_status="$(xxd -p -l 8 "$out_file" | tr -d '\n')"
  local actual_status_dec; actual_status_dec="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$actual_status'))[0])")"

  if [[ "$exp_status" != "0" ]]; then
    if [[ "$actual_status_dec" == "$exp_status" ]]; then
      printf "  %-30s OK   status=%d (rejected)\n" "$name" "$exp_status"
      return 0
    else
      printf "  %-30s FAIL status=%d expected=%d\n" "$name" "$actual_status_dec" "$exp_status"
      return 1
    fi
  fi

  local actual_len_le; actual_len_le="$(dd if="$out_file" bs=1 skip=8 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local actual_len; actual_len="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$actual_len_le'))[0])")"
  local expected_hex; expected_hex="$(cat "$exp_hex_file")"
  local expected_len; expected_len=$(( ${#expected_hex} / 2 ))
  local cmp_len=$expected_len
  if [[ $cmp_len -gt 240 ]]; then cmp_len=240; fi
  local actual_hex; actual_hex="$(dd if="$out_file" bs=1 skip=16 count="$cmp_len" 2>/dev/null | xxd -p | tr -d '\n')"
  local expected_prefix="${expected_hex:0:$((2 * cmp_len))}"

  if [[ "$actual_status_dec" == "0" \
       && "$actual_len" == "$expected_len" \
       && "$actual_hex" == "$expected_prefix" ]]; then
    printf "  %-30s OK   idx_a=%d idx_b=%d len=%d\n" "$name" "$idx_a" "$idx_b" "$expected_len"
    return 0
  else
    printf "  %-30s FAIL status=%d actual_len=%d expected_len=%d\n" "$name" "$actual_status_dec" "$actual_len" "$expected_len"
    printf "      actual:   %s...\n" "${actual_hex:0:80}"
    printf "      expected: %s...\n" "${expected_prefix:0:80}"
    return 1
  fi
}

HASH_A="a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0"
HASH_B="a0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0"

FAILED=0
# Typical 2-tx block: slots 0 and 8 active (rlp(0)/rlp(1) divergence)
run_case "slots_0_and_8"     0 "$HASH_A" 8 "$HASH_B" 0 || FAILED=1
# Slots 0 and 1 active
run_case "slots_0_and_1"     0 "$HASH_A" 1 "$HASH_B" 0 || FAILED=1
# Slot 15 (last child) + slot 16 (value)
run_case "slots_15_and_16"   15 "$HASH_A" 16 "$HASH_B" 0 || FAILED=1
# Short inline children (no 0xa0 prefix)
run_case "inline_at_0_and_5" 0 "c4820080" 5 "85deadbeef00" 0 || FAILED=1
# Mixed: hashed at 0, inline at 8
run_case "hashed_inline"     0 "$HASH_A" 8 "c4820080" 0 || FAILED=1
# Rejection: idx_a == idx_b
run_case "duplicate_indices" 3 "$HASH_A" 3 "$HASH_B" 1 || FAILED=1
# Rejection: idx >= 17
run_case "idx_a_oob"         17 "$HASH_A" 0 "$HASH_B" 1 || FAILED=1
run_case "idx_b_oob"         0 "$HASH_A" 20 "$HASH_B" 1 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: mpt_branch_payload_two_slots assembles the 17-slot payload correctly"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
