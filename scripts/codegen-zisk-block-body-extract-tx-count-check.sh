#!/usr/bin/env bash
# codegen-zisk-block-body-extract-tx-count-check.sh -- PR-K223.
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

echo "==> emit zisk_block_body_extract_tx_count ELF"
lake exe codegen --program zisk_block_body_extract_tx_count --halt linux93 \
  -o gen-out/zisk_block_body_extract_tx_count

REPO_ROOT="$(pwd)"

run_case() {
  local name="$1" tx_count="$2"

  local in_file="$REPO_ROOT/gen-out/zisk_block_body_extract_tx_count_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_block_body_extract_tx_count_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys, rlp
tx = bytes.fromhex('f8500184ee6b280082520894aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa881bc16d674ec80000801ba01111111111111111111111111111111111111111111111111111111111111111a02222222222222222222222222222222222222222222222222222222222222222')
n = $tx_count
txs = [tx for _ in range(n)]
body_rlp = rlp.encode([txs, [], []])
with open(sys.argv[1], 'wb') as f:
    record = struct.pack('<Q', len(body_rlp)) + body_rlp
    f.write(record)
    pad = (-len(record)) % 8
    if pad: f.write(b'\x00' * pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_block_body_extract_tx_count.elf \
    -i "$in_file" -o "$out_file" -n 1000000 \
    >"$REPO_ROOT/gen-out/zisk_block_body_extract_tx_count_${name}.emu.log" 2>&1 || true

  local status_le; status_le="$(xxd -p -l 8 "$out_file" | tr -d '\n')"
  local c_le; c_le="$(dd if="$out_file" bs=1 skip=8 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local status; status="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$status_le'))[0])")"
  local count; count="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$c_le'))[0])")"

  if [[ "$status" == "0" && "$count" == "$tx_count" ]]; then
    printf "  %-26s OK   count=%s\n" "$name" "$count"
    return 0
  else
    printf "  %-26s FAIL status=%s count=%s/%s\n" "$name" "$status" "$count" "$tx_count"
    return 1
  fi
}

FAILED=0
run_case "zero_txs"   0 || FAILED=1
run_case "one_tx"     1 || FAILED=1
run_case "two_txs"    2 || FAILED=1
run_case "five_txs"   5 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: block_body_extract_tx_count returns the tx-list cardinality"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
