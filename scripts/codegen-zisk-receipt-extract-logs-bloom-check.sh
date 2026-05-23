#!/usr/bin/env bash
# codegen-zisk-receipt-extract-logs-bloom-check.sh -- PR-K152.
#
# Extract the 256-byte logs_bloom field (field 2) from a receipt RLP.
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

echo "==> emit zisk_receipt_extract_logs_bloom ELF"
lake exe codegen --program zisk_receipt_extract_logs_bloom --halt linux93 \
  -o gen-out/zisk_receipt_extract_logs_bloom

REPO_ROOT="$(pwd)"

# run_case <name> <status> <cumulative_gas> <bloom_hex_256B> <logs_json>
run_case() {
  local name="$1" status="$2" gas="$3" bloom="$4" logs="$5"

  local in_file="$REPO_ROOT/gen-out/zisk_receipt_extract_logs_bloom_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_receipt_extract_logs_bloom_${name}.output"
  local exp_hex_file="$REPO_ROOT/gen-out/zisk_receipt_extract_logs_bloom_${name}.expected.hex"

  uv run --directory execution-specs --quiet python3 -c "
import json, struct, sys, rlp
status = $status
gas = $gas
bloom = bytes.fromhex('$bloom')
assert len(bloom) == 256, len(bloom)
raw_logs = json.loads('''$logs''')
logs = []
for addr_hex, topic_hexes, data_hex in raw_logs:
    addr = bytes.fromhex(addr_hex)
    topics = [bytes.fromhex(t) for t in topic_hexes]
    data = bytes.fromhex(data_hex)
    logs.append([addr, topics, data])
receipt = [status, gas, bloom, logs]
receipt_rlp = rlp.encode(receipt)
with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(receipt_rlp)))
    f.write(receipt_rlp)
    pad = (-(8 + len(receipt_rlp))) % 8
    if pad: f.write(b'\x00' * pad)
with open(sys.argv[2], 'w') as f:
    f.write(bloom.hex())
" "$in_file" "$exp_hex_file"

  "$ZISKEMU" -e gen-out/zisk_receipt_extract_logs_bloom.elf \
    -i "$in_file" -o "$out_file" -n 1000000 \
    >"$REPO_ROOT/gen-out/zisk_receipt_extract_logs_bloom_${name}.emu.log" 2>&1 || true

  # Output is 256 bytes of bloom (ziskemu output cap == bloom size).
  local actual_bloom; actual_bloom="$(xxd -p -c 256 "$out_file" | tr -d '\n')"
  local expected; expected="$(cat "$exp_hex_file")"

  if [[ "$actual_bloom" == "$expected" ]]; then
    local nbits; nbits="$(python3 -c "print(bin(int('$actual_bloom', 16)).count('1'))")"
    printf "  %-30s OK   bits_set=%d\n" "$name" "$nbits"
    return 0
  else
    printf "  %-30s FAIL\n" "$name"
    printf "      actual:   %s...\n" "${actual_bloom:0:80}"
    printf "      expected: %s...\n" "${expected:0:80}"
    return 1
  fi
}

ZERO_BLOOM="$(python3 -c "print('00' * 256)")"
ALL_FF_BLOOM="$(python3 -c "print('ff' * 256)")"
RAND_BLOOM="$(python3 -c "import os; print(os.urandom(256).hex())")"

A1="aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
T0="1111111111111111111111111111111111111111111111111111111111111111"

FAILED=0
# Zero bloom (no logs case)
run_case "zero_bloom"    1 21000 "$ZERO_BLOOM" "[]" || FAILED=1
# All-ones bloom (degenerate stress)
run_case "all_ones"      1 1000000 "$ALL_FF_BLOOM" "[]" || FAILED=1
# Random bloom with realistic logs (logs not validated by this helper)
run_case "random_bloom_one_log" 1 100000 "$RAND_BLOOM" "[[\"$A1\", [\"$T0\"], \"deadbeef\"]]" || FAILED=1
# Status=0 (failed tx)
run_case "failed_tx"     0 50000 "$ZERO_BLOOM" "[]" || FAILED=1
# Large cumulative_gas
run_case "max_gas"       1 30000000 "$ZERO_BLOOM" "[]" || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: receipt_extract_logs_bloom recovers the 256-byte field"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
