#!/usr/bin/env bash
# codegen-zisk-chain-body-total-tx-count-check.sh -- PR-K227.
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

echo "==> emit zisk_chain_body_total_tx_count ELF"
lake exe codegen --program zisk_chain_body_total_tx_count --halt linux93 \
  -o gen-out/zisk_chain_body_total_tx_count

REPO_ROOT="$(pwd)"

# run_case <name> <tx_counts_py> <exp_sum>
run_case() {
  local name="$1" counts="$2" exp_sum="$3"

  local in_file="$REPO_ROOT/gen-out/zisk_chain_body_total_tx_count_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_chain_body_total_tx_count_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys, rlp
tx = bytes.fromhex('f8500184ee6b280082520894aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa881bc16d674ec80000801ba01111111111111111111111111111111111111111111111111111111111111111a02222222222222222222222222222222222222222222222222222222222222222')
counts = $counts
bodies = [rlp.encode([[tx for _ in range(c)], [], []]) for c in counts]
N = len(bodies)
lengths = b''.join(struct.pack('<Q', len(b)) for b in bodies)
flat = b''.join(bodies)

with open(sys.argv[1], 'wb') as f:
    record = struct.pack('<Q', N) + lengths + flat
    f.write(record)
    pad = (-len(record)) % 8
    if pad: f.write(b'\x00' * pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_chain_body_total_tx_count.elf \
    -i "$in_file" -o "$out_file" -n 5000000 \
    >"$REPO_ROOT/gen-out/zisk_chain_body_total_tx_count_${name}.emu.log" 2>&1 || true

  local s_le; s_le="$(dd if="$out_file" bs=1 skip=8 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local actual; actual="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$s_le'))[0])")"
  if [[ "$actual" == "$exp_sum" ]]; then
    printf "  %-26s OK   sum=%s\n" "$name" "$actual"
    return 0
  else
    printf "  %-26s FAIL actual=%s expected=%s\n" "$name" "$actual" "$exp_sum"
    return 1
  fi
}

FAILED=0
run_case "empty_chain"   "[]" 0 || FAILED=1
run_case "single_empty"  "[0]" 0 || FAILED=1
run_case "single_two"    "[2]" 2 || FAILED=1
run_case "three_blocks"  "[1,2,3]" 6 || FAILED=1
run_case "five_blocks"   "[0,1,2,3,4]" 10 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: chain_body_total_tx_count sums tx counts across bodies"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
