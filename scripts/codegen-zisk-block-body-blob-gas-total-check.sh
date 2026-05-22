#!/usr/bin/env bash
# codegen-zisk-block-body-blob-gas-total-check.sh -- PR-K89.
#
# Sum blob_gas_used over all EIP-4844 txs in a block body.
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

echo "==> emit zisk_block_body_blob_gas_total ELF"
lake exe codegen --program zisk_block_body_blob_gas_total --halt linux93 \
  -o gen-out/zisk_block_body_blob_gas_total

REPO_ROOT="$(pwd)"

# run_case <name> <tx_spec_json> <gas_per_blob>
# tx_spec_json: list of {"type": "legacy"|"eip4844", "blobs": N} entries.
run_case() {
  local name="$1" spec="$2" gpb="$3"

  local in_file="$REPO_ROOT/gen-out/zisk_block_body_blob_gas_total_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_block_body_blob_gas_total_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import json, struct, sys, rlp
spec = json.loads('''$spec''')
gpb = $gpb
ALICE = bytes([0xaa]*20)
R = int.from_bytes(bytes([0x11]*32), 'big')
S = int.from_bytes(bytes([0x22]*32), 'big')

txs = []
total = 0
for entry in spec:
    if entry['type'] == 'legacy':
        # legacy tx, RLP list
        tx = [1, 10**9, 21000, ALICE, 10**18, b'', 27, R, S]
        txs.append(tx)
    elif entry['type'] == 'eip4844':
        n = entry['blobs']
        H = bytes([0x01] + [0xab]*31)
        inner = [
            1, 7, 10**9, 2*10**9, 21000,
            ALICE, 10**18, b'', [],
            1, [H]*n, 0,
            R, S,
        ]
        inner_rlp = rlp.encode(inner)
        # Typed tx is encoded in outer list as a byte string [0x03 || inner]
        typed_bytes = b'\x03' + inner_rlp
        txs.append(typed_bytes)
        total += n * gpb
    else:
        raise ValueError(entry['type'])

# Block body = [transactions, ommers, withdrawals]
body = [txs, [], []]
body_rlp = rlp.encode(body)

with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(body_rlp)))
    f.write(struct.pack('<Q', gpb))
    f.write(body_rlp)
    pad = (-(16 + len(body_rlp))) % 8
    if pad: f.write(b'\x00' * pad)

with open(sys.argv[1] + '.expected.txt', 'w') as f:
    f.write(str(total))
" "$in_file"

  local expected; expected="$(cat "$in_file.expected.txt")"

  "$ZISKEMU" -e gen-out/zisk_block_body_blob_gas_total.elf \
    -i "$in_file" -o "$out_file" -n 5000000 \
    >"$REPO_ROOT/gen-out/zisk_block_body_blob_gas_total_${name}.emu.log" 2>&1 || true

  local actual_status; actual_status="$(xxd -p -l 8 "$out_file" | tr -d '\n')"
  local actual_total; actual_total="$(dd if="$out_file" bs=1 skip=8 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local exp_le; exp_le="$(python3 -c "print(int('$expected').to_bytes(8, 'little').hex())")"

  if [[ "$actual_status" == "0000000000000000" && "$actual_total" == "$exp_le" ]]; then
    printf "  %-32s OK   total=%s\n" "$name" "$expected"
    return 0
  else
    printf "  %-32s FAIL status=0x%s total=0x%s (expected %s)\n" "$name" "$actual_status" "$actual_total" "$expected"
    return 1
  fi
}

GPB=131072

FAILED=0
run_case "empty"                     "[]"                                                "$GPB" || FAILED=1
run_case "only_legacy"               '[{"type":"legacy"}]'                               "$GPB" || FAILED=1
run_case "only_two_legacy"           '[{"type":"legacy"},{"type":"legacy"}]'             "$GPB" || FAILED=1
run_case "one_eip4844_one_blob"      '[{"type":"eip4844","blobs":1}]'                    "$GPB" || FAILED=1
run_case "one_eip4844_six_blobs"     '[{"type":"eip4844","blobs":6}]'                    "$GPB" || FAILED=1
run_case "two_eip4844_mixed"         '[{"type":"eip4844","blobs":2},{"type":"eip4844","blobs":4}]' "$GPB" || FAILED=1
run_case "mixed_legacy_and_blob"     '[{"type":"legacy"},{"type":"eip4844","blobs":3},{"type":"legacy"}]' "$GPB" || FAILED=1
run_case "interleaved_three_eip4844" '[{"type":"eip4844","blobs":1},{"type":"legacy"},{"type":"eip4844","blobs":2},{"type":"legacy"},{"type":"eip4844","blobs":1}]' "$GPB" || FAILED=1
run_case "custom_gpb"                '[{"type":"eip4844","blobs":3}]'                    1000   || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: block_body_blob_gas_total = sum over type-3 txs"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
