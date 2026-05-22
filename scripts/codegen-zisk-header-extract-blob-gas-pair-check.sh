#!/usr/bin/env bash
# codegen-zisk-header-extract-blob-gas-pair-check.sh -- PR-K90.
#
# Extract Cancun blob_gas_used / excess_blob_gas from an Amsterdam header.
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

echo "==> emit zisk_header_extract_blob_gas_pair ELF"
lake exe codegen --program zisk_header_extract_blob_gas_pair --halt linux93 \
  -o gen-out/zisk_header_extract_blob_gas_pair

REPO_ROOT="$(pwd)"

# run_case <name> <blob_gas_used> <excess_blob_gas> [<truncate_field>]
# truncate_field: if "premerge", drop fields 17/18 to test failure
run_case() {
  local name="$1" bgu="$2" ebg="$3" trunc="${4:-}"
  local exp_status; if [[ "$trunc" == "drop17" ]]; then exp_status=1; elif [[ "$trunc" == "drop18" ]]; then exp_status=2; else exp_status=0; fi

  local in_file="$REPO_ROOT/gen-out/zisk_header_extract_blob_gas_pair_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_header_extract_blob_gas_pair_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys, rlp
bgu, ebg, trunc = $bgu, $ebg, '$trunc'
fields = [
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
    bgu,                        # 17 blob_gas_used
    ebg,                        # 18 excess_blob_gas
    bytes(32),                  # 19 parent_beacon_block_root
    bytes(32),                  # 20 requests_hash
    bytes(32),                  # 21 block_access_list_hash
]
if trunc == 'drop17':
    fields = fields[:17]
elif trunc == 'drop18':
    fields = fields[:18]
header_rlp = rlp.encode(fields)
with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(header_rlp)))
    f.write(header_rlp)
    pad = (-(8 + len(header_rlp))) % 8
    if pad: f.write(b'\x00' * pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_header_extract_blob_gas_pair.elf \
    -i "$in_file" -o "$out_file" -n 1000000 \
    >"$REPO_ROOT/gen-out/zisk_header_extract_blob_gas_pair_${name}.emu.log" 2>&1 || true

  local actual_status; actual_status="$(xxd -p -l 8 "$out_file" | tr -d '\n')"
  local actual_bgu; actual_bgu="$(dd if="$out_file" bs=1 skip=8 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local actual_ebg; actual_ebg="$(dd if="$out_file" bs=1 skip=16 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local exp_status_le; exp_status_le="$(python3 -c "print(int('$exp_status').to_bytes(8, 'little').hex())")"

  if [[ "$exp_status" == "0" ]]; then
    local exp_bgu; exp_bgu="$(python3 -c "print(int('$bgu').to_bytes(8, 'little').hex())")"
    local exp_ebg; exp_ebg="$(python3 -c "print(int('$ebg').to_bytes(8, 'little').hex())")"
    if [[ "$actual_status" == "$exp_status_le" && "$actual_bgu" == "$exp_bgu" && "$actual_ebg" == "$exp_ebg" ]]; then
      printf "  %-32s OK   bgu=%d ebg=%d\n" "$name" "$bgu" "$ebg"
      return 0
    else
      printf "  %-32s FAIL  status=0x%s bgu=0x%s ebg=0x%s\n" "$name" "$actual_status" "$actual_bgu" "$actual_ebg"
      return 1
    fi
  else
    if [[ "$actual_status" == "$exp_status_le" ]]; then
      printf "  %-32s OK   status=%d (rejected as expected)\n" "$name" "$exp_status"
      return 0
    else
      printf "  %-32s FAIL  expected status=%d got 0x%s\n" "$name" "$exp_status" "$actual_status"
      return 1
    fi
  fi
}

FAILED=0
run_case "zero_blob_zero_excess"  0          0                    || FAILED=1
run_case "one_blob"                131072     0                    || FAILED=1
run_case "six_blobs"               786432     0                    || FAILED=1
run_case "max_cap_nine_blobs"      1179648    0                    || FAILED=1
run_case "with_excess"             393216     100000               || FAILED=1
run_case "big_excess"              0          18446744073709551615 || FAILED=1
run_case "missing_field_17"        0          0          drop17    || FAILED=1
run_case "missing_field_18"        0          0          drop18    || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: header_extract_blob_gas_pair returns (blob_gas_used, excess_blob_gas)"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
