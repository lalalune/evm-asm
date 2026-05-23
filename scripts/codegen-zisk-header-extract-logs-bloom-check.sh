#!/usr/bin/env bash
# codegen-zisk-header-extract-logs-bloom-check.sh -- PR-K153.
#
# Extract the 256-byte logs_bloom field (field 6) from a block header RLP.
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

echo "==> emit zisk_header_extract_logs_bloom ELF"
lake exe codegen --program zisk_header_extract_logs_bloom --halt linux93 \
  -o gen-out/zisk_header_extract_logs_bloom

REPO_ROOT="$(pwd)"

# run_case <name> <fork_tag> <bloom_hex_256B>
# fork_tag selects which fields are present:
#   "merge"     -> 15 fields, post-merge, no base_fee
#   "london"    -> 16 fields, base_fee_per_gas
#   "shanghai"  -> 17 fields, withdrawals_root
#   "cancun"    -> 20 fields, blob_gas_used + excess + beacon_root
#   "prague"    -> 21 fields, +requests_hash
run_case() {
  local name="$1" fork="$2" bloom="$3"

  local in_file="$REPO_ROOT/gen-out/zisk_header_extract_logs_bloom_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_header_extract_logs_bloom_${name}.output"
  local exp_hex_file="$REPO_ROOT/gen-out/zisk_header_extract_logs_bloom_${name}.expected.hex"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys, rlp
fork = '$fork'
bloom = bytes.fromhex('$bloom')
assert len(bloom) == 256
H32 = bytes([0xaa] * 32)
ADDR = bytes([0xbb] * 20)
# Common pre-bloom fields (0..5).
hdr = [
    H32,                                        # parent_hash
    bytes.fromhex('1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347'),  # ommers_hash (empty)
    ADDR,                                       # coinbase
    H32,                                        # state_root
    H32,                                        # transactions_root
    H32,                                        # receipts_root
    bloom,                                      # field 6: logs_bloom
    0,                                          # difficulty
    18000000,                                   # number
    30000000,                                   # gas_limit
    21000,                                      # gas_used
    1700000000,                                 # timestamp
    b'',                                        # extra_data
    H32,                                        # prev_randao
    b'\\x00' * 8,                                # nonce
]
if fork in ('london', 'shanghai', 'cancun', 'prague'):
    hdr.append(7 * 10**9)                       # base_fee_per_gas
if fork in ('shanghai', 'cancun', 'prague'):
    hdr.append(H32)                             # withdrawals_root
if fork in ('cancun', 'prague'):
    hdr += [131072, 786432, H32]                # blob_gas_used, excess_blob_gas, beacon_root
if fork == 'prague':
    hdr.append(H32)                             # requests_hash

header_rlp = rlp.encode(hdr)
with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(header_rlp)))
    f.write(header_rlp)
    pad = (-(8 + len(header_rlp))) % 8
    if pad: f.write(b'\x00' * pad)
with open(sys.argv[2], 'w') as f:
    f.write(bloom.hex())
" "$in_file" "$exp_hex_file"

  "$ZISKEMU" -e gen-out/zisk_header_extract_logs_bloom.elf \
    -i "$in_file" -o "$out_file" -n 1000000 \
    >"$REPO_ROOT/gen-out/zisk_header_extract_logs_bloom_${name}.emu.log" 2>&1 || true

  local actual; actual="$(xxd -p -c 256 "$out_file" | tr -d '\n')"
  local expected; expected="$(cat "$exp_hex_file")"

  if [[ "$actual" == "$expected" ]]; then
    local nbits; nbits="$(python3 -c "print(bin(int('$actual', 16)).count('1'))")"
    printf "  %-30s OK   fork=%s bits_set=%d\n" "$name" "$fork" "$nbits"
    return 0
  else
    printf "  %-30s FAIL fork=%s\n" "$name" "$fork"
    printf "      actual:   %s...\n" "${actual:0:80}"
    printf "      expected: %s...\n" "${expected:0:80}"
    return 1
  fi
}

ZERO_BLOOM="$(python3 -c "print('00' * 256)")"
ALL_FF_BLOOM="$(python3 -c "print('ff' * 256)")"
RAND_BLOOM="$(python3 -c "import os; print(os.urandom(256).hex())")"

FAILED=0
run_case "merge_zero_bloom"    merge    "$ZERO_BLOOM"   || FAILED=1
run_case "london_zero_bloom"   london   "$ZERO_BLOOM"   || FAILED=1
run_case "shanghai_random"     shanghai "$RAND_BLOOM"   || FAILED=1
run_case "cancun_random"       cancun   "$RAND_BLOOM"   || FAILED=1
run_case "prague_random"       prague   "$RAND_BLOOM"   || FAILED=1
run_case "cancun_all_ones"     cancun   "$ALL_FF_BLOOM" || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: header_extract_logs_bloom finds the field across all fork shapes"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
