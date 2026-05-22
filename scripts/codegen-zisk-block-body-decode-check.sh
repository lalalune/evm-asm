#!/usr/bin/env bash
# codegen-zisk-block-body-decode-check.sh -- PR-K83.
#
# Decode a post-Shanghai block body into three (offset, length)
# pairs for txs, ommers, withdrawals.
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

echo "==> emit zisk_block_body_decode ELF"
lake exe codegen --program zisk_block_body_decode --halt linux93 \
  -o gen-out/zisk_block_body_decode

REPO_ROOT="$(pwd)"

# run_case <name> <txs_json> <ommers_json> <withdrawals_json>
run_case() {
  local name="$1" txs="$2" ommers="$3" wds="$4"

  local in_file="$REPO_ROOT/gen-out/zisk_block_body_decode_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_block_body_decode_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_block_body_decode_${name}.expected"

  uv run --directory execution-specs --quiet python3 -c "
import json, struct, sys
import rlp

txs_raw     = json.loads('''$txs''')
ommers_raw  = json.loads('''$ommers''')
wds_raw     = json.loads('''$wds''')

# Convert hex strings → bytes; lists recurse.
def conv(x):
    if isinstance(x, str):
        return bytes.fromhex(x)
    if isinstance(x, list):
        return [conv(e) for e in x]
    return x

txs    = conv(txs_raw)
ommers = conv(ommers_raw)
wds    = []
for w in wds_raw:
    idx, vi, addr_hex, amt = w
    wds.append([idx, vi, bytes.fromhex(addr_hex), amt])

body_rlp = rlp.encode([txs, ommers, wds])
with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(body_rlp)))
    f.write(body_rlp)
    pad = (-(8 + len(body_rlp))) % 8
    if pad:
        f.write(b'\x00' * pad)

# Expected struct: (txs_off, txs_len, ommers_off, ommers_len, wd_off, wd_len)
def field_offset(items, idx):
    payload = b''.join(rlp.encode(it) for it in items)
    if len(payload) < 56:
        prefix_len = 1
    else:
        length_bits = (len(payload).bit_length() + 7) // 8
        prefix_len = 1 + length_bits
    offset = prefix_len
    for i in range(idx):
        offset += len(rlp.encode(items[i]))
    item_rlp = rlp.encode(items[idx])
    if len(item_rlp) == 1 and item_rlp[0] < 0x80:
        return offset, 1
    elif item_rlp[0] < 0xb8:
        return offset + 1, item_rlp[0] - 0x80
    elif item_rlp[0] < 0xc0:
        lol = item_rlp[0] - 0xb7
        return (offset + 1 + lol,
                int.from_bytes(item_rlp[1:1+lol], 'big'))
    else:
        return offset, len(item_rlp)

items = [txs, ommers, wds]
exp = struct.pack('<Q', 0)  # status
for i in range(3):
    o, l = field_offset(items, i)
    exp += struct.pack('<Q', o)
    exp += struct.pack('<Q', l)

with open(sys.argv[2], 'wb') as f:
    f.write(exp)
" "$in_file" "$exp_file"

  "$ZISKEMU" -e gen-out/zisk_block_body_decode.elf \
    -i "$in_file" -o "$out_file" -n 500000 \
    >"$REPO_ROOT/gen-out/zisk_block_body_decode_${name}.emu.log" 2>&1 || true

  local actual; actual="$(xxd -p -l 56 "$out_file" | tr -d '\n')"
  local expected; expected="$(xxd -p -l 56 "$exp_file" | tr -d '\n')"

  if [[ "$actual" == "$expected" ]]; then
    printf "  %-30s OK\n" "$name"
    return 0
  else
    printf "  %-30s FAIL\n    expected: %s\n    actual:   %s\n" "$name" "$expected" "$actual"
    return 1
  fi
}

ALICE="aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"

FAILED=0
# Empty block: 0 txs, 0 ommers, 0 withdrawals
run_case "empty_block" "[]" "[]" "[]"  || FAILED=1

# Withdrawals only
run_case "withdrawals_only" "[]" "[]" "[[0, 1, \"$ALICE\", 1000000000]]"  || FAILED=1

# Transactions only (txs as raw bytes — typed-tx envelopes)
TX_LEGACY="f8650184ee6b280082520894aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa881bc16d674ec80000801ba01111111111111111111111111111111111111111111111111111111111111111a02222222222222222222222222222222222222222222222222222222222222222"
run_case "one_legacy_tx" "[\"$TX_LEGACY\"]" "[]" "[]"  || FAILED=1

# Mainnet shape: 2 txs, 0 ommers, 1 withdrawal
run_case "mixed_block" \
  "[\"$TX_LEGACY\", \"$TX_LEGACY\"]" "[]" \
  "[[100, 12345, \"$ALICE\", 32000000000]]"  || FAILED=1

# Many withdrawals
SIX_WDS="$(python3 -c "
import json
addr = '$ALICE'
ws = [[i, i+1000, addr, (i+1) * 10**9] for i in range(6)]
print(json.dumps(ws))
")"
run_case "six_withdrawals" "[]" "[]" "$SIX_WDS"  || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: block_body_decode returns 3 (offset, length) pairs"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
