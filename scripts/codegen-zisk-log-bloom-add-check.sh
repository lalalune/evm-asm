#!/usr/bin/env bash
# codegen-zisk-log-bloom-add-check.sh -- PR-K149.
#
# Apply a full log's bloom contributions (address + each topic)
# to a 256-byte Ethereum log bloom filter.
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

echo "==> emit zisk_log_bloom_add ELF"
lake exe codegen --program zisk_log_bloom_add --halt linux93 \
  -o gen-out/zisk_log_bloom_add

REPO_ROOT="$(pwd)"

# run_case <name> <address_hex> <topics_json>  <data_hex>
# topics_json is a JSON list of 32-byte hex strings (without quotes
# transformation since each is a hex literal).
run_case() {
  local name="$1" addr="$2" topics="$3" data="$4"

  local in_file="$REPO_ROOT/gen-out/zisk_log_bloom_add_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_log_bloom_add_${name}.output"
  local exp_hex_file="$REPO_ROOT/gen-out/zisk_log_bloom_add_${name}.expected.hex"

  uv run --directory execution-specs --quiet python3 -c "
import json, struct, sys, rlp
try:
    from Crypto.Hash import keccak
    def keccak256(b):
        h = keccak.new(digest_bits=256); h.update(b); return h.digest()
except Exception:
    import sha3
    def keccak256(b): return sha3.keccak_256(b).digest()

addr = bytes.fromhex('$addr')
topics = [bytes.fromhex(t) for t in json.loads('$topics')]
data = bytes.fromhex('$data')
log_rlp = rlp.encode([addr, topics, data])
bloom = bytearray(256)
def add(b, v):
    h = keccak256(v)
    for idx in (0, 2, 4):
        raw = int.from_bytes(h[idx:idx+2], 'big') & 0x07FF
        bit = 0x07FF - raw
        b[bit // 8] |= 1 << (7 - (bit % 8))
add(bloom, addr)
for t in topics:
    add(bloom, t)
with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(log_rlp)))
    f.write(log_rlp)
    pad = (-(8 + len(log_rlp))) % 8
    if pad: f.write(b'\x00' * pad)
with open(sys.argv[2], 'w') as f:
    f.write(bytes(bloom).hex())
" "$in_file" "$exp_hex_file"

  "$ZISKEMU" -e gen-out/zisk_log_bloom_add.elf \
    -i "$in_file" -o "$out_file" -n 5000000 \
    >"$REPO_ROOT/gen-out/zisk_log_bloom_add_${name}.emu.log" 2>&1 || true

  local actual; actual="$(xxd -p -c 256 "$out_file" | tr -d '\n')"
  local expected; expected="$(cat "$exp_hex_file")"

  if [[ "$actual" == "$expected" ]]; then
    local nbits; nbits="$(python3 -c "print(bin(int('$actual', 16)).count('1'))")"
    printf "  %-30s OK   topics=%d bits_set=%d\n" "$name" "$(python3 -c "import json; print(len(json.loads('$topics')))")" "$nbits"
    return 0
  else
    printf "  %-30s FAIL\n" "$name"
    printf "      actual:   %s...\n" "${actual:0:80}"
    printf "      expected: %s...\n" "${expected:0:80}"
    return 1
  fi
}

TOPIC0="1111111111111111111111111111111111111111111111111111111111111111"
TOPIC1="2222222222222222222222222222222222222222222222222222222222222222"
TOPIC2="3333333333333333333333333333333333333333333333333333333333333333"
TOPIC3="4444444444444444444444444444444444444444444444444444444444444444"

FAILED=0
# LOG0: just address, no topics
run_case "log0_no_topics" \
  "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa" \
  "[]" \
  "deadbeef" || FAILED=1
# LOG1: one topic
run_case "log1_one_topic" \
  "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb" \
  "[\"$TOPIC0\"]" \
  "" || FAILED=1
# LOG2: two topics
run_case "log2_two_topics" \
  "cccccccccccccccccccccccccccccccccccccccc" \
  "[\"$TOPIC0\", \"$TOPIC1\"]" \
  "00112233" || FAILED=1
# LOG3
run_case "log3_three_topics" \
  "dddddddddddddddddddddddddddddddddddddddd" \
  "[\"$TOPIC0\", \"$TOPIC1\", \"$TOPIC2\"]" \
  "" || FAILED=1
# LOG4 (max topics)
run_case "log4_four_topics" \
  "eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee" \
  "[\"$TOPIC0\", \"$TOPIC1\", \"$TOPIC2\", \"$TOPIC3\"]" \
  "$(python3 -c "print('ab' * 64)")" || FAILED=1
# Long data (data is *not* bloomed; should not affect output)
run_case "log0_long_data" \
  "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa" \
  "[]" \
  "$(python3 -c "print('cd' * 100)")" || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: log_bloom_add accumulates address + topics; ignores data"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
