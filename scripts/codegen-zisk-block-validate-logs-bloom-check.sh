#!/usr/bin/env bash
# codegen-zisk-block-validate-logs-bloom-check.sh -- PR-K159.
#
# End-to-end block-level logs_bloom validation:
#   1. Extract header.logs_bloom
#   2. Compute block bloom from receipts list
#   3. Compare; return is_valid
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

echo "==> emit zisk_block_validate_logs_bloom ELF"
lake exe codegen --program zisk_block_validate_logs_bloom --halt linux93 \
  -o gen-out/zisk_block_validate_logs_bloom

REPO_ROOT="$(pwd)"

# run_case <name> <bloom_in_header_hex> <receipts_json> <expected_status> <expected_is_valid>
run_case() {
  local name="$1" header_bloom="$2" receipts="$3" exp_status="$4" exp_valid="$5"

  local in_file="$REPO_ROOT/gen-out/zisk_block_validate_logs_bloom_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_block_validate_logs_bloom_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import json, struct, sys, rlp
header_bloom = bytes.fromhex('$header_bloom')
assert len(header_bloom) == 256
raw_receipts = json.loads('''$receipts''')
receipts = []
for r in raw_receipts:
    receipts.append([r['status'], r['gas'], bytes.fromhex(r['bloom']), []])
receipts_list_rlp = rlp.encode(receipts)

# Build a minimal post-merge header with our bloom at field 6.
H32 = bytes([0xaa] * 32)
ADDR = bytes([0xbb] * 20)
hdr = [
    H32,                                # parent_hash
    bytes.fromhex('1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347'),
    ADDR,                               # coinbase
    H32, H32, H32,                      # state, tx, receipts roots
    header_bloom,                       # field 6
    0, 18000000, 30000000, 21000,
    1700000000, b'', H32, b'\\x00' * 8,
    7 * 10**9, H32,
]
header_rlp = rlp.encode(hdr)

with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(header_rlp)))
    f.write(struct.pack('<Q', len(receipts_list_rlp)))
    f.write(header_rlp + receipts_list_rlp)
    pad = (-(16 + len(header_rlp) + len(receipts_list_rlp))) % 8
    if pad: f.write(b'\x00' * pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_block_validate_logs_bloom.elf \
    -i "$in_file" -o "$out_file" -n 5000000 \
    >"$REPO_ROOT/gen-out/zisk_block_validate_logs_bloom_${name}.emu.log" 2>&1 || true

  local actual_status; actual_status="$(xxd -p -l 8 "$out_file" | tr -d '\n')"
  local actual_valid_le; actual_valid_le="$(dd if="$out_file" bs=1 skip=8 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local actual_status_dec; actual_status_dec="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$actual_status'))[0])")"
  local actual_valid; actual_valid="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$actual_valid_le'))[0])")"

  if [[ "$actual_status_dec" == "$exp_status" && "$actual_valid" == "$exp_valid" ]]; then
    printf "  %-30s OK   status=%d is_valid=%d\n" "$name" "$exp_status" "$exp_valid"
    return 0
  else
    printf "  %-30s FAIL status=%d (expected %d) is_valid=%d (expected %d)\n" "$name" "$actual_status_dec" "$exp_status" "$actual_valid" "$exp_valid"
    return 1
  fi
}

ZERO_BLOOM="$(python3 -c "print('00' * 256)")"
B_BIT0="$(python3 -c "b=bytearray(256); b[0]=0x80; print(bytes(b).hex())")"
B_BIT1="$(python3 -c "b=bytearray(256); b[1]=0x40; print(bytes(b).hex())")"
B_BIT0_BIT1="$(python3 -c "b=bytearray(256); b[0]=0x80; b[1]=0x40; print(bytes(b).hex())")"

FAILED=0
# Match: empty receipts list, zero bloom in header.
run_case "match_empty_zero"     "$ZERO_BLOOM"    "[]" 0 1 || FAILED=1
# Match: single receipt's bloom equals header bloom.
run_case "match_single"         "$B_BIT0"        "[{\"status\":1,\"gas\":21000,\"bloom\":\"$B_BIT0\"}]" 0 1 || FAILED=1
# Match: two receipts OR'd into header bloom.
run_case "match_two_or"         "$B_BIT0_BIT1"   "[{\"status\":1,\"gas\":21000,\"bloom\":\"$B_BIT0\"}, {\"status\":1,\"gas\":42000,\"bloom\":\"$B_BIT1\"}]" 0 1 || FAILED=1
# Mismatch: header bloom doesn't match computed.
run_case "mismatch_wrong_bit"   "$B_BIT1"        "[{\"status\":1,\"gas\":21000,\"bloom\":\"$B_BIT0\"}]" 0 0 || FAILED=1
# Mismatch: header says zero but receipts contribute bits.
run_case "mismatch_underreport" "$ZERO_BLOOM"    "[{\"status\":1,\"gas\":21000,\"bloom\":\"$B_BIT0\"}]" 0 0 || FAILED=1
# Mismatch: header has extra bits.
run_case "mismatch_overreport"  "$B_BIT0"        "[]" 0 0 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: block_validate_logs_bloom predicate matches Python OR-accumulation"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
