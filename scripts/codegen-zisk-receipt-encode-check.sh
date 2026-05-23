#!/usr/bin/env bash
# codegen-zisk-receipt-encode-check.sh -- PR-K156.
#
# Encode a tx receipt as RLP: rlp([status, cumulative_gas, logs_bloom, logs])
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

echo "==> emit zisk_receipt_encode ELF"
lake exe codegen --program zisk_receipt_encode --halt linux93 \
  -o gen-out/zisk_receipt_encode

REPO_ROOT="$(pwd)"

# run_case <name> <status> <cumulative_gas> <bloom_hex_256B> <logs_json>
# Note: ziskemu output cap is 256 B; very short receipts work.
run_case() {
  local name="$1" status="$2" gas="$3" bloom="$4" logs="$5"

  local in_file="$REPO_ROOT/gen-out/zisk_receipt_encode_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_receipt_encode_${name}.output"
  local exp_hex_file="$REPO_ROOT/gen-out/zisk_receipt_encode_${name}.expected.hex"

  uv run --directory execution-specs --quiet python3 -c "
import json, struct, sys, rlp
status = $status
gas = $gas
bloom = bytes.fromhex('$bloom')
assert len(bloom) == 256
raw_logs = json.loads('''$logs''')
logs = []
for addr_hex, topic_hexes, data_hex in raw_logs:
    addr = bytes.fromhex(addr_hex)
    topics = [bytes.fromhex(t) for t in topic_hexes]
    data = bytes.fromhex(data_hex)
    logs.append([addr, topics, data])
logs_rlp = rlp.encode(logs)
receipt_rlp = rlp.encode([status, gas, bloom, logs])

with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', status))
    f.write(struct.pack('<Q', gas))
    f.write(bloom)
    f.write(struct.pack('<Q', len(logs_rlp)))
    f.write(logs_rlp)
    pad = (-(280 + len(logs_rlp))) % 8
    if pad: f.write(b'\x00' * pad)
with open(sys.argv[2], 'w') as f:
    f.write(receipt_rlp.hex())
" "$in_file" "$exp_hex_file"

  "$ZISKEMU" -e gen-out/zisk_receipt_encode.elf \
    -i "$in_file" -o "$out_file" -n 5000000 \
    >"$REPO_ROOT/gen-out/zisk_receipt_encode_${name}.emu.log" 2>&1 || true

  local actual_status; actual_status="$(xxd -p -l 8 "$out_file" | tr -d '\n')"
  local actual_len_le; actual_len_le="$(dd if="$out_file" bs=1 skip=8 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local actual_len; actual_len="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$actual_len_le'))[0])")"
  local expected_hex; expected_hex="$(cat "$exp_hex_file")"
  local expected_len; expected_len=$(( ${#expected_hex} / 2 ))
  # Output cap = 256 B; we have 8B status + 8B length + up to 240 B of encoded bytes.
  # For receipts longer than 240 B we only compare the first 240 bytes.
  local cmp_len=$expected_len
  if [[ $cmp_len -gt 240 ]]; then cmp_len=240; fi
  local actual_hex; actual_hex="$(dd if="$out_file" bs=1 skip=16 count="$cmp_len" 2>/dev/null | xxd -p | tr -d '\n')"
  local expected_prefix; expected_prefix="${expected_hex:0:$((2 * cmp_len))}"

  if [[ "$actual_status" == "0000000000000000" \
       && "$actual_len" == "$expected_len" \
       && "$actual_hex" == "$expected_prefix" ]]; then
    printf "  %-30s OK   len=%d (compared %d B)\n" "$name" "$expected_len" "$cmp_len"
    return 0
  else
    printf "  %-30s FAIL status=0x%s actual_len=%d expected_len=%d\n" "$name" "$actual_status" "$actual_len" "$expected_len"
    printf "      actual:   %s...\n" "${actual_hex:0:80}"
    printf "      expected: %s...\n" "${expected_prefix:0:80}"
    return 1
  fi
}

ZERO_BLOOM="$(python3 -c "print('00' * 256)")"
RAND_BLOOM="$(python3 -c "import os; print(os.urandom(256).hex())")"

A1="aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
T0="1111111111111111111111111111111111111111111111111111111111111111"

FAILED=0
# Empty receipt (no logs)
run_case "empty_logs_zero_bloom" 1 21000 "$ZERO_BLOOM" "[]" || FAILED=1
# Failed-tx receipt (status=0)
run_case "failed_tx"             0 50000 "$ZERO_BLOOM" "[]" || FAILED=1
# Receipt with random bloom but no logs
run_case "random_bloom_no_logs"  1 30000 "$RAND_BLOOM" "[]" || FAILED=1
# Receipt with one log (small data) and zero bloom
run_case "one_log_small"         1 70000 "$ZERO_BLOOM" "[[\"$A1\", [\"$T0\"], \"\"]]" || FAILED=1
# Cumulative gas > 24 bits (multi-byte RLP)
run_case "large_gas"             1 30000000 "$ZERO_BLOOM" "[]" || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: receipt_encode matches Python rlp.encode([status, gas, bloom, logs])"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
