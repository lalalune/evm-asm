#!/usr/bin/env bash
# codegen-zisk-header-minimal-decode-check.sh -- PR-K38.
#
# Extract (parent_hash, state_root, number, timestamp) from an
# RLP-encoded Ethereum block header.
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

echo "==> emit zisk_header_minimal_decode ELF"
lake exe codegen --program zisk_header_minimal_decode --halt linux93 \
  -o gen-out/zisk_header_minimal_decode

REPO_ROOT="$(pwd)"

run_case() {
  local name="$1" parent_hex="$2" state_root_hex="$3" number="$4" timestamp="$5" with_real_header="${6:-no}"

  local in_file="$REPO_ROOT/gen-out/zisk_header_minimal_decode_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_header_minimal_decode_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_header_minimal_decode_${name}.expected"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys
import rlp

parent_hash = bytes.fromhex('$parent_hex')
state_root = bytes.fromhex('$state_root_hex')
number = $number
timestamp = $timestamp

if '$with_real_header' == 'yes':
    from ethereum.crypto.hash import Hash32
    from ethereum_types.bytes import Bytes, Bytes8, Bytes32
    from ethereum_types.numeric import U64, U256, Uint
    from ethereum.forks.amsterdam.blocks import Header
    from ethereum.forks.amsterdam.fork_types import Bloom
    h = Header(
        parent_hash=Hash32(parent_hash),
        ommers_hash=Hash32(b'\x22' * 32),
        coinbase=Bytes(b'\x33' * 20),
        state_root=Hash32(state_root),
        transactions_root=Hash32(b'\x55' * 32),
        receipt_root=Hash32(b'\x66' * 32),
        bloom=Bloom(b'\x00' * 256),
        difficulty=Uint(0),
        number=Uint(number),
        gas_limit=Uint(0x1c9c380),
        gas_used=Uint(0x100),
        timestamp=U256(timestamp),
        extra_data=Bytes(b'test'),
        prev_randao=Bytes32(b'\x77' * 32),
        nonce=Bytes8(b'\x00' * 8),
        base_fee_per_gas=Uint(0x07),
        withdrawals_root=Hash32(b'\x88' * 32),
        blob_gas_used=U64(0),
        excess_blob_gas=U64(0),
        parent_beacon_block_root=Hash32(b'\x99' * 32),
        requests_hash=Hash32(b'\xaa' * 32),
        block_access_list_hash=Hash32(b'\xbb' * 32),
    )
    header_rlp = rlp.encode(h)
else:
    # Synthetic minimal header: just enough fields to reach number/timestamp.
    # Build a 12-field RLP list with the right indices populated.
    fields = [
        parent_hash,       # 0: parent_hash
        b'\x22' * 32,      # 1: ommers_hash
        b'\x33' * 20,      # 2: coinbase
        state_root,        # 3: state_root
        b'\x55' * 32,      # 4: transactions_root
        b'\x66' * 32,      # 5: receipts_root
        b'\x00' * 256,     # 6: bloom
        0,                  # 7: difficulty
        number,            # 8: number
        0x1c9c380,         # 9: gas_limit
        0x100,             # 10: gas_used
        timestamp,         # 11: timestamp
    ]
    header_rlp = rlp.encode(fields)

with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(header_rlp)))
    f.write(header_rlp)
    pad = (-(8 + len(header_rlp))) % 8
    if pad:
        f.write(b'\x00' * pad)

# Expected: status u64 + 96-byte struct.
expected = struct.pack('<Q', 0)
expected += parent_hash
expected += state_root
expected += struct.pack('<Q', number)
expected += struct.pack('<Q', timestamp)
with open(sys.argv[2], 'wb') as f:
    f.write(expected)
" "$in_file" "$exp_file"

  "$ZISKEMU" -e gen-out/zisk_header_minimal_decode.elf \
    -i "$in_file" -o "$out_file" -n 500000 \
    >"$REPO_ROOT/gen-out/zisk_header_minimal_decode_${name}.emu.log" 2>&1 || true

  local exp_size; exp_size="$(stat -c%s "$exp_file")"
  local actual expected
  actual="$(xxd -p -l "$exp_size" "$out_file" 2>/dev/null | tr -d '\n')"
  expected="$(xxd -p -l "$exp_size" "$exp_file" 2>/dev/null | tr -d '\n')"

  if [[ "$actual" == "$expected" ]]; then
    printf "  %-26s OK   number=%d ts=%d\n" "$name" "$number" "$timestamp"
    return 0
  else
    printf "  %-26s FAIL\n    expected: %s\n    actual:   %s\n" "$name" "$expected" "$actual"
    return 1
  fi
}

PARENT="$(printf '11%.0s' $(seq 1 32))"
STATE_ROOT="$(printf '44%.0s' $(seq 1 32))"

FAILED=0
run_case "synthetic_genesis"      "$PARENT" "$STATE_ROOT" 0          0                          || FAILED=1
run_case "synthetic_mid"          "$PARENT" "$STATE_ROOT" 1234567    1700000000                 || FAILED=1
run_case "synthetic_big"          "$PARENT" "$STATE_ROOT" 18446744073709551615 4294967295       || FAILED=1
# Additional shapes
run_case "different_parent"       "$(printf 'cc%.0s' $(seq 1 32))" "$STATE_ROOT" 100 1000000000 || FAILED=1
run_case "different_state_root"   "$PARENT" "$(printf 'dd%.0s' $(seq 1 32))" 200 2000000000     || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: header_minimal_decode extracts (parent_hash, state_root, number, timestamp)"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
