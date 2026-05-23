#!/usr/bin/env bash
# codegen-zisk-block-logs-bloom-from-receipts-list-check.sh -- PR-K158.
#
# Compute the block-level logs_bloom from an RLP list of receipts.
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

echo "==> emit zisk_block_logs_bloom_from_receipts_list ELF"
lake exe codegen --program zisk_block_logs_bloom_from_receipts_list --halt linux93 \
  -o gen-out/zisk_block_logs_bloom_from_receipts_list

REPO_ROOT="$(pwd)"

# run_case <name> <receipts_json>
# receipts_json = JSON list of receipts, each as
#   {"status":1, "gas":21000, "bloom":"00...ff", "logs":[]}
run_case() {
  local name="$1" receipts="$2"

  local in_file="$REPO_ROOT/gen-out/zisk_block_logs_bloom_from_receipts_list_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_block_logs_bloom_from_receipts_list_${name}.output"
  local exp_hex_file="$REPO_ROOT/gen-out/zisk_block_logs_bloom_from_receipts_list_${name}.expected.hex"

  uv run --directory execution-specs --quiet python3 -c "
import json, struct, sys, rlp
raw = json.loads('''$receipts''')
receipts = []
for r in raw:
    status = r['status']
    gas = r['gas']
    bloom = bytes.fromhex(r['bloom'])
    assert len(bloom) == 256
    logs_raw = r.get('logs', [])
    logs = []
    for addr_hex, topic_hexes, data_hex in logs_raw:
        addr = bytes.fromhex(addr_hex)
        topics = [bytes.fromhex(t) for t in topic_hexes]
        data = bytes.fromhex(data_hex)
        logs.append([addr, topics, data])
    receipts.append([status, gas, bloom, logs])
receipts_list_rlp = rlp.encode(receipts)

expected_bloom = bytearray(256)
for _status, _gas, bloom, _logs in receipts:
    for i in range(256):
        expected_bloom[i] |= bloom[i]

with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(receipts_list_rlp)))
    f.write(receipts_list_rlp)
    pad = (-(8 + len(receipts_list_rlp))) % 8
    if pad: f.write(b'\x00' * pad)
with open(sys.argv[2], 'w') as f:
    f.write(bytes(expected_bloom).hex())
" "$in_file" "$exp_hex_file"

  "$ZISKEMU" -e gen-out/zisk_block_logs_bloom_from_receipts_list.elf \
    -i "$in_file" -o "$out_file" -n 5000000 \
    >"$REPO_ROOT/gen-out/zisk_block_logs_bloom_from_receipts_list_${name}.emu.log" 2>&1 || true

  local actual; actual="$(xxd -p -c 256 "$out_file" | tr -d '\n')"
  local expected; expected="$(cat "$exp_hex_file")"

  if [[ "$actual" == "$expected" ]]; then
    local nbits; nbits="$(python3 -c "print(bin(int('$actual', 16)).count('1'))")"
    local n; n="$(python3 -c "import json; print(len(json.loads('''$receipts''')))")"
    printf "  %-30s OK   n_receipts=%d bits=%d\n" "$name" "$n" "$nbits"
    return 0
  else
    printf "  %-30s FAIL\n" "$name"
    printf "      actual:   %s...\n" "${actual:0:80}"
    printf "      expected: %s...\n" "${expected:0:80}"
    return 1
  fi
}

ZERO_BLOOM="$(python3 -c "print('00' * 256)")"
ALL_FF_BLOOM="$(python3 -c "print('ff' * 256)")"
# Bloom with a single bit set in byte 0
B_BIT0="$(python3 -c "b=bytearray(256); b[0]=0x80; print(bytes(b).hex())")"
# Bloom with a single bit set in byte 255
B_BIT_LAST="$(python3 -c "b=bytearray(256); b[255]=0x01; print(bytes(b).hex())")"
# Bloom with bit set in the middle
B_BIT_MID="$(python3 -c "b=bytearray(256); b[128]=0x40; print(bytes(b).hex())")"

FAILED=0
# Empty receipts list -> zero bloom
run_case "empty"     "[]" || FAILED=1
# Single receipt -> output == receipt bloom
run_case "one"       "[{\"status\":1,\"gas\":21000,\"bloom\":\"$B_BIT0\",\"logs\":[]}]" || FAILED=1
# Two receipts, disjoint blooms -> OR
run_case "two_disjoint" "[{\"status\":1,\"gas\":21000,\"bloom\":\"$B_BIT0\",\"logs\":[]}, {\"status\":1,\"gas\":42000,\"bloom\":\"$B_BIT_LAST\",\"logs\":[]}]" || FAILED=1
# Three receipts, all different bit positions
run_case "three_disjoint" "[{\"status\":1,\"gas\":21000,\"bloom\":\"$B_BIT0\",\"logs\":[]}, {\"status\":1,\"gas\":42000,\"bloom\":\"$B_BIT_MID\",\"logs\":[]}, {\"status\":0,\"gas\":50000,\"bloom\":\"$B_BIT_LAST\",\"logs\":[]}]" || FAILED=1
# Mix of full and zero blooms
run_case "mixed_full_zero" "[{\"status\":1,\"gas\":21000,\"bloom\":\"$ALL_FF_BLOOM\",\"logs\":[]}, {\"status\":1,\"gas\":42000,\"bloom\":\"$ZERO_BLOOM\",\"logs\":[]}]" || FAILED=1
# Idempotency: same bloom twice
run_case "duplicates" "[{\"status\":1,\"gas\":21000,\"bloom\":\"$B_BIT0\",\"logs\":[]}, {\"status\":1,\"gas\":42000,\"bloom\":\"$B_BIT0\",\"logs\":[]}]" || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: block_logs_bloom_from_receipts_list OR-accumulates receipt blooms"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
