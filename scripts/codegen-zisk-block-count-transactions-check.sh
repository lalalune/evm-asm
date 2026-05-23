#!/usr/bin/env bash
# codegen-zisk-block-count-transactions-check.sh -- PR-K125.
#
# Count transactions in a block body.
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

echo "==> emit zisk_block_count_transactions ELF"
lake exe codegen --program zisk_block_count_transactions --halt linux93 \
  -o gen-out/zisk_block_count_transactions

REPO_ROOT="$(pwd)"

# run_case <name> <tx_count>
run_case() {
  local name="$1" tx_count="$2"

  local in_file="$REPO_ROOT/gen-out/zisk_block_count_transactions_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_block_count_transactions_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys, rlp
n = $tx_count
ALICE = bytes([0xaa]*20)
R = int.from_bytes(bytes([0x11]*32), 'big')
S = int.from_bytes(bytes([0x22]*32), 'big')

txs = []
for _ in range(n):
    tx = [1, 10**9, 21000, ALICE, 10**18, b'', 27, R, S]
    txs.append(rlp.encode(tx))

body_rlp = rlp.encode([txs, [], []])
with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(body_rlp)))
    f.write(body_rlp)
    pad = (-(8 + len(body_rlp))) % 8
    if pad: f.write(b'\x00' * pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_block_count_transactions.elf \
    -i "$in_file" -o "$out_file" -n 5000000 \
    >"$REPO_ROOT/gen-out/zisk_block_count_transactions_${name}.emu.log" 2>&1 || true

  local actual_status; actual_status="$(xxd -p -l 8 "$out_file" | tr -d '\n')"
  local actual_count_le; actual_count_le="$(dd if="$out_file" bs=1 skip=8 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local actual_count; actual_count="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$actual_count_le'))[0])")"

  if [[ "$actual_status" == "0000000000000000" && "$actual_count" == "$tx_count" ]]; then
    printf "  %-32s OK   count=%d\n" "$name" "$tx_count"
    return 0
  else
    printf "  %-32s FAIL status=0x%s count=%d expected=%d\n" "$name" "$actual_status" "$actual_count" "$tx_count"
    return 1
  fi
}

FAILED=0
run_case "empty"          0    || FAILED=1
run_case "one_tx"         1    || FAILED=1
run_case "two_tx"         2    || FAILED=1
run_case "fifteen_tx"     15   || FAILED=1
run_case "fifty_tx"       50   || FAILED=1
run_case "two_hundred"    200  || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: block_count_transactions returns len(block.transactions)"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
