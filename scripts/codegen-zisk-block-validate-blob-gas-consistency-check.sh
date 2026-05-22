#!/usr/bin/env bash
# codegen-zisk-block-validate-blob-gas-consistency-check.sh -- PR-K91.
#
# Cancun consensus check: header.blob_gas_used == sum(tx blob gas).
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

echo "==> emit zisk_block_validate_blob_gas_consistency ELF"
lake exe codegen --program zisk_block_validate_blob_gas_consistency --halt linux93 \
  -o gen-out/zisk_block_validate_blob_gas_consistency

REPO_ROOT="$(pwd)"

# run_case <name> <header_bgu> <tx_spec_json> <gas_per_blob> <expected_status>
run_case() {
  local name="$1" hbgu="$2" spec="$3" gpb="$4" exp="$5"

  local in_file="$REPO_ROOT/gen-out/zisk_block_validate_blob_gas_consistency_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_block_validate_blob_gas_consistency_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import json, struct, sys, rlp
hbgu = $hbgu
spec = json.loads('''$spec''')
gpb = $gpb
ALICE = bytes([0xaa]*20)
R = int.from_bytes(bytes([0x11]*32), 'big')
S = int.from_bytes(bytes([0x22]*32), 'big')

# Build header: 22 fields; only field 17 (blob_gas_used) varies.
header_fields = [
    bytes(32),                  # 0 parent_hash
    bytes(32),                  # 1 ommers_hash
    bytes(20),                  # 2 coinbase
    bytes(32),                  # 3 state_root
    bytes(32),                  # 4 transactions_root
    bytes(32),                  # 5 receipt_root
    bytes(256),                 # 6 bloom
    0,                          # 7 difficulty
    1,                          # 8 number
    30_000_000,                 # 9 gas_limit
    100_000,                    # 10 gas_used
    1700000000,                 # 11 timestamp
    b'',                        # 12 extra_data
    bytes(32),                  # 13 prev_randao
    bytes(8),                   # 14 nonce
    10**9,                      # 15 base_fee_per_gas
    bytes(32),                  # 16 withdrawals_root
    hbgu,                       # 17 blob_gas_used
    0,                          # 18 excess_blob_gas
    bytes(32),                  # 19 parent_beacon_block_root
    bytes(32),                  # 20 requests_hash
    bytes(32),                  # 21 block_access_list_hash
]
header_rlp = rlp.encode(header_fields)

# Build body.
txs = []
for entry in spec:
    if entry['type'] == 'legacy':
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
        typed_bytes = b'\x03' + inner_rlp
        txs.append(typed_bytes)
    else:
        raise ValueError(entry['type'])

body_rlp = rlp.encode([txs, [], []])

with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(header_rlp)))
    f.write(struct.pack('<Q', len(body_rlp)))
    f.write(struct.pack('<Q', gpb))
    f.write(header_rlp)
    f.write(body_rlp)
    total = 24 + len(header_rlp) + len(body_rlp)
    pad = (-total) % 8
    if pad: f.write(b'\x00' * pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_block_validate_blob_gas_consistency.elf \
    -i "$in_file" -o "$out_file" -n 5000000 \
    >"$REPO_ROOT/gen-out/zisk_block_validate_blob_gas_consistency_${name}.emu.log" 2>&1 || true

  local actual_status; actual_status="$(xxd -p -l 8 "$out_file" | tr -d '\n')"
  local exp_status_le; exp_status_le="$(python3 -c "print(int('$exp').to_bytes(8, 'little').hex())")"

  if [[ "$actual_status" == "$exp_status_le" ]]; then
    printf "  %-40s OK   status=%d\n" "$name" "$exp"
    return 0
  else
    printf "  %-40s FAIL status=0x%s expected=%d\n" "$name" "$actual_status" "$exp"
    return 1
  fi
}

GPB=131072

FAILED=0
# Match cases (status=0)
run_case "empty_block_zero_bgu"          0 '[]'                                                "$GPB" 0 || FAILED=1
run_case "legacy_only_zero_bgu"          0 '[{"type":"legacy"},{"type":"legacy"}]'              "$GPB" 0 || FAILED=1
run_case "one_blob_match"                131072 '[{"type":"eip4844","blobs":1}]'               "$GPB" 0 || FAILED=1
run_case "six_blob_match"                786432 '[{"type":"eip4844","blobs":6}]'               "$GPB" 0 || FAILED=1
run_case "two_eip4844_mixed_match"       786432 '[{"type":"eip4844","blobs":2},{"type":"eip4844","blobs":4}]' "$GPB" 0 || FAILED=1
run_case "legacy_and_blob_match"         393216 '[{"type":"legacy"},{"type":"eip4844","blobs":3}]' "$GPB" 0 || FAILED=1

# Mismatch cases (status=2)
run_case "mismatch_header_too_high"      262144 '[{"type":"eip4844","blobs":1}]'               "$GPB" 2 || FAILED=1
run_case "mismatch_header_too_low"       0      '[{"type":"eip4844","blobs":1}]'               "$GPB" 2 || FAILED=1
run_case "mismatch_off_by_one_blob"      262144 '[{"type":"eip4844","blobs":1}]'               "$GPB" 2 || FAILED=1
run_case "mismatch_legacy_with_nonzero"  131072 '[{"type":"legacy"}]'                          "$GPB" 2 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: block_validate_blob_gas_consistency matches header to body sum"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
