#!/usr/bin/env bash
# codegen-zisk-block-compute-tx-hashes-check.sh -- PR-K97.
#
# Walk the block body's transactions list and compute keccak256 of each.
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

echo "==> emit zisk_block_compute_tx_hashes ELF"
lake exe codegen --program zisk_block_compute_tx_hashes --halt linux93 \
  -o gen-out/zisk_block_compute_tx_hashes

REPO_ROOT="$(pwd)"

# run_case <name> <tx_spec_json>
# tx_spec_json: list of {"type": "legacy"|"eip1559"|"eip4844", "blobs": N (only for eip4844)}
run_case() {
  local name="$1" spec="$2"

  local in_file="$REPO_ROOT/gen-out/zisk_block_compute_tx_hashes_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_block_compute_tx_hashes_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import json, struct, sys, rlp
from Crypto.Hash import keccak
spec = json.loads('''$spec''')
ALICE = bytes([0xaa]*20)
R = int.from_bytes(bytes([0x11]*32), 'big')
S = int.from_bytes(bytes([0x22]*32), 'big')

tx_encoded_list = []
expected_hashes = []
for entry in spec:
    t = entry['type']
    if t == 'legacy':
        tx = [1, 10**9, 21000, ALICE, 10**18, b'', 27, R, S]
        b = rlp.encode(tx)
    elif t == 'eip1559':
        inner = [1, 7, 10**9, 2*10**9, 21000, ALICE, 10**18, b'', [], 1, R, S]
        b = b'\x02' + rlp.encode(inner)
    elif t == 'eip4844':
        n = entry['blobs']
        H = bytes([0x01] + [0xab]*31)
        inner = [
            1, 7, 10**9, 2*10**9, 21000,
            ALICE, 10**18, b'', [],
            1, [H]*n, 0, R, S,
        ]
        b = b'\x03' + rlp.encode(inner)
    else:
        raise ValueError(t)
    tx_encoded_list.append(b)
    expected_hashes.append(keccak.new(digest_bits=256).update(b).digest())

txs_rlp = rlp.encode(tx_encoded_list)

with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(txs_rlp)))
    f.write(txs_rlp)
    pad = (-(8 + len(txs_rlp))) % 8
    if pad: f.write(b'\x00' * pad)

with open(sys.argv[1] + '.expected', 'wb') as f:
    f.write(b''.join(expected_hashes))
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_block_compute_tx_hashes.elf \
    -i "$in_file" -o "$out_file" -n 50000000 \
    >"$REPO_ROOT/gen-out/zisk_block_compute_tx_hashes_${name}.emu.log" 2>&1 || true

  local actual_status; actual_status="$(xxd -p -l 8 "$out_file" | tr -d '\n')"
  local actual_count_le; actual_count_le="$(dd if="$out_file" bs=1 skip=8 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local exp_count; exp_count="$(python3 -c "import json; print(len(json.loads('''$spec''')))")"
  local exp_count_le; exp_count_le="$(python3 -c "print(int('$exp_count').to_bytes(8, 'little').hex())")"

  if [[ "$actual_status" != "0000000000000000" ]]; then
    printf "  %-32s FAIL  status=0x%s\n" "$name" "$actual_status"
    return 1
  fi
  if [[ "$actual_count_le" != "$exp_count_le" ]]; then
    printf "  %-32s FAIL  count=0x%s expected=%d\n" "$name" "$actual_count_le" "$exp_count"
    return 1
  fi
  local total_bytes=$((exp_count * 32))
  if [[ "$exp_count" == "0" ]]; then
    printf "  %-32s OK   N=0\n" "$name"
    return 0
  fi
  local actual_hashes; actual_hashes="$(dd if="$out_file" bs=1 skip=16 count="$total_bytes" 2>/dev/null | xxd -p | tr -d '\n')"
  local expected_hashes; expected_hashes="$(xxd -p "$in_file.expected" | tr -d '\n')"
  if [[ "$actual_hashes" == "$expected_hashes" ]]; then
    printf "  %-32s OK   N=%d\n" "$name" "$exp_count"
    return 0
  else
    printf "  %-32s FAIL  N=%d hash mismatch\n" "$name" "$exp_count"
    printf "    expected: %s\n" "${expected_hashes:0:64}.."
    printf "    actual:   %s\n" "${actual_hashes:0:64}.."
    return 1
  fi
}

FAILED=0
run_case "empty"              '[]'                                               || FAILED=1
run_case "one_legacy"         '[{"type":"legacy"}]'                              || FAILED=1
run_case "two_legacy"         '[{"type":"legacy"},{"type":"legacy"}]'            || FAILED=1
run_case "one_eip1559"        '[{"type":"eip1559"}]'                             || FAILED=1
run_case "one_eip4844"        '[{"type":"eip4844","blobs":1}]'                   || FAILED=1
run_case "mixed_legacy_blob"  '[{"type":"legacy"},{"type":"eip4844","blobs":3}]' || FAILED=1
run_case "five_mixed" \
  '[{"type":"legacy"},{"type":"eip1559"},{"type":"eip4844","blobs":2},{"type":"legacy"},{"type":"eip4844","blobs":1}]' || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: block_compute_tx_hashes returns keccak256 of each encoded tx"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
