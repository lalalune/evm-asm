#!/usr/bin/env bash
# codegen-zisk-logs-list-bloom-add-check.sh -- PR-K150.
#
# OR every log's bloom contribution from an RLP-encoded logs list
# into a 256-byte bloom buffer.
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

echo "==> emit zisk_logs_list_bloom_add ELF"
lake exe codegen --program zisk_logs_list_bloom_add --halt linux93 \
  -o gen-out/zisk_logs_list_bloom_add

REPO_ROOT="$(pwd)"

# run_case <name> <logs_json>
# logs_json: list of [address_hex, topics_list_hex, data_hex]
run_case() {
  local name="$1" logs="$2"

  local in_file="$REPO_ROOT/gen-out/zisk_logs_list_bloom_add_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_logs_list_bloom_add_${name}.output"
  local exp_hex_file="$REPO_ROOT/gen-out/zisk_logs_list_bloom_add_${name}.expected.hex"

  uv run --directory execution-specs --quiet python3 -c "
import json, struct, sys, rlp
try:
    from Crypto.Hash import keccak
    def keccak256(b):
        h = keccak.new(digest_bits=256); h.update(b); return h.digest()
except Exception:
    import sha3
    def keccak256(b): return sha3.keccak_256(b).digest()

raw_logs = json.loads('''$logs''')
logs = []
for addr_hex, topic_hexes, data_hex in raw_logs:
    addr = bytes.fromhex(addr_hex)
    topics = [bytes.fromhex(t) for t in topic_hexes]
    data = bytes.fromhex(data_hex)
    logs.append([addr, topics, data])
logs_rlp = rlp.encode(logs)

bloom = bytearray(256)
def add(b, v):
    h = keccak256(v)
    for idx in (0, 2, 4):
        raw = int.from_bytes(h[idx:idx+2], 'big') & 0x07FF
        bit = 0x07FF - raw
        b[bit // 8] |= 1 << (7 - (bit % 8))
for addr, topics, _data in logs:
    add(bloom, addr)
    for t in topics:
        add(bloom, t)

with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(logs_rlp)))
    f.write(logs_rlp)
    pad = (-(8 + len(logs_rlp))) % 8
    if pad: f.write(b'\x00' * pad)
with open(sys.argv[2], 'w') as f:
    f.write(bytes(bloom).hex())
" "$in_file" "$exp_hex_file"

  "$ZISKEMU" -e gen-out/zisk_logs_list_bloom_add.elf \
    -i "$in_file" -o "$out_file" -n 10000000 \
    >"$REPO_ROOT/gen-out/zisk_logs_list_bloom_add_${name}.emu.log" 2>&1 || true

  local actual; actual="$(xxd -p -c 256 "$out_file" | tr -d '\n')"
  local expected; expected="$(cat "$exp_hex_file")"

  if [[ "$actual" == "$expected" ]]; then
    local nbits; nbits="$(python3 -c "print(bin(int('$actual', 16)).count('1'))")"
    local n_logs; n_logs="$(python3 -c "import json; print(len(json.loads('''$logs''')))")"
    printf "  %-30s OK   n_logs=%d bits_set=%d\n" "$name" "$n_logs" "$nbits"
    return 0
  else
    printf "  %-30s FAIL\n" "$name"
    printf "      actual:   %s...\n" "${actual:0:80}"
    printf "      expected: %s...\n" "${expected:0:80}"
    return 1
  fi
}

A1="aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
A2="bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"
A3="cccccccccccccccccccccccccccccccccccccccc"
T0="1111111111111111111111111111111111111111111111111111111111111111"
T1="2222222222222222222222222222222222222222222222222222222222222222"
T2="3333333333333333333333333333333333333333333333333333333333333333"

FAILED=0
# Empty logs list: bloom unchanged (still zero).
run_case "empty"        "[]" || FAILED=1
# Single log, no topics.
run_case "one_log_log0" "[[\"$A1\", [], \"deadbeef\"]]" || FAILED=1
# Single log, one topic.
run_case "one_log_log1" "[[\"$A1\", [\"$T0\"], \"\"]]" || FAILED=1
# Multiple logs.
run_case "three_logs"   "[[\"$A1\", [\"$T0\"], \"\"], [\"$A2\", [\"$T0\", \"$T1\"], \"deadbeef\"], [\"$A3\", [], \"00\"]]" || FAILED=1
# Many logs with topics (stress).
run_case "five_logs_mixed" \
  "[[\"$A1\", [\"$T0\", \"$T1\", \"$T2\"], \"\"], [\"$A2\", [], \"\"], [\"$A3\", [\"$T0\"], \"\"], [\"$A1\", [\"$T1\", \"$T2\"], \"\"], [\"$A2\", [\"$T0\", \"$T1\", \"$T2\"], \"cafebabe\"]]" || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: logs_list_bloom_add accumulates every log's bloom contribution"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
