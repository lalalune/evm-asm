#!/usr/bin/env bash
# codegen-zisk-block-summary-check.sh -- PR-K86.
#
# One-pass block body audit: tx_count + withdrawal_total + ommers_empty.
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

echo "==> emit zisk_block_summary ELF"
lake exe codegen --program zisk_block_summary --halt linux93 \
  -o gen-out/zisk_block_summary

REPO_ROOT="$(pwd)"

# run_case <name> <txs_json> <ommers_json> <wds_json>
run_case() {
  local name="$1" txs="$2" ommers="$3" wds="$4"

  local in_file="$REPO_ROOT/gen-out/zisk_block_summary_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_block_summary_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_block_summary_${name}.expected"

  uv run --directory execution-specs --quiet python3 -c "
import json, struct, sys, rlp
txs_raw    = json.loads('''$txs''')
ommers_raw = json.loads('''$ommers''')
wds_raw    = json.loads('''$wds''')
def conv(x):
    if isinstance(x, str): return bytes.fromhex(x)
    if isinstance(x, list): return [conv(e) for e in x]
    return x
txs = conv(txs_raw)
ommers = conv(ommers_raw)
wds = []
for w in wds_raw:
    idx, vi, addr_hex, amt = w
    wds.append([idx, vi, bytes.fromhex(addr_hex), amt])

body_rlp = rlp.encode([txs, ommers, wds])
with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(body_rlp)))
    f.write(body_rlp)
    pad = (-(8 + len(body_rlp))) % 8
    if pad: f.write(b'\x00' * pad)

# Expected: status + tx_count + wd_total + ommers_empty
exp_total = sum(w[3] for w in wds_raw)
exp_ommers_empty = 1 if len(ommers_raw) == 0 else 0
exp_tx_count = len(txs_raw)
with open(sys.argv[2], 'wb') as f:
    f.write(struct.pack('<Q', 0))                  # status
    f.write(struct.pack('<Q', exp_tx_count))
    f.write(struct.pack('<Q', exp_total))
    f.write(struct.pack('<Q', exp_ommers_empty))
" "$in_file" "$exp_file"

  "$ZISKEMU" -e gen-out/zisk_block_summary.elf \
    -i "$in_file" -o "$out_file" -n 1000000 \
    >"$REPO_ROOT/gen-out/zisk_block_summary_${name}.emu.log" 2>&1 || true

  local actual; actual="$(xxd -p -l 32 "$out_file" | tr -d '\n')"
  local expected; expected="$(xxd -p -l 32 "$exp_file" | tr -d '\n')"
  if [[ "$actual" == "$expected" ]]; then
    local tcount wtotal oempty
    tcount="$(python3 -c "import json; print(len(json.loads('''$txs''')))")"
    wtotal="$(python3 -c "import json; print(sum(w[3] for w in json.loads('''$wds''')))")"
    oempty="$(python3 -c "import json; print(1 if len(json.loads('''$ommers''')) == 0 else 0)")"
    printf "  %-30s OK   txs=%d wd_total=%d ommers_empty=%d\n" "$name" "$tcount" "$wtotal" "$oempty"
    return 0
  else
    printf "  %-30s FAIL\n    expected: %s\n    actual:   %s\n" "$name" "$expected" "$actual"
    return 1
  fi
}

ALICE="aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
TX_LEGACY="f8650184ee6b280082520894aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa881bc16d674ec80000801ba01111111111111111111111111111111111111111111111111111111111111111a02222222222222222222222222222222222222222222222222222222222222222"

FAILED=0
# Empty block
run_case "empty_block"            "[]"                 "[]" "[]"                          || FAILED=1
# Withdrawals only, post-merge
run_case "wd_only_post_merge"     "[]"                 "[]" \
  "[[0, 1, \"$ALICE\", 1000000000]]" || FAILED=1
# Txs only
run_case "txs_only"               "[\"$TX_LEGACY\"]"   "[]" "[]"                          || FAILED=1
# Mixed: 2 txs, 1 withdrawal
run_case "mixed_block" \
  "[\"$TX_LEGACY\", \"$TX_LEGACY\"]" "[]" \
  "[[100, 12345, \"$ALICE\", 32000000000]]" || FAILED=1
# Mainnet shape: 16 withdrawals
SIXTEEN_WD="$(python3 -c "
import json
addr = '$ALICE'
print(json.dumps([[i, i+1000, addr, (i+1) * 10**9] for i in range(16)]))
")"
run_case "mainnet_full_wds"       "[]" "[]" "$SIXTEEN_WD"  || FAILED=1
# Pre-merge: ommers non-empty
run_case "pre_merge_with_ommers"  "[]" "[[]]" "[]"     || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: block_summary extracts tx_count + wd_total + ommers_empty"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
