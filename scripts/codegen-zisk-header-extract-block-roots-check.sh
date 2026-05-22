#!/usr/bin/env bash
# codegen-zisk-header-extract-block-roots-check.sh -- PR-K95.
#
# Extract transactions_root / receipt_root / withdrawals_root from header.
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

echo "==> emit zisk_header_extract_block_roots ELF"
lake exe codegen --program zisk_header_extract_block_roots --halt linux93 \
  -o gen-out/zisk_header_extract_block_roots

REPO_ROOT="$(pwd)"

# run_case <name> <tx_root_hex> <rec_root_hex> <wd_root_hex> [truncate]
run_case() {
  local name="$1" tx="$2" rec="$3" wd="$4" trunc="${5:-}"
  local exp_status; if [[ "$trunc" == "drop16" ]]; then exp_status=3; else exp_status=0; fi

  local in_file="$REPO_ROOT/gen-out/zisk_header_extract_block_roots_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_header_extract_block_roots_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys, rlp
tx = bytes.fromhex('$tx')
rec = bytes.fromhex('$rec')
wd = bytes.fromhex('$wd')
trunc = '$trunc'
fields = [
    bytes(32), bytes(32), bytes(20), bytes(32),
    tx,                         # 4 transactions_root
    rec,                        # 5 receipt_root
    bytes(256), 0, 1, 30_000_000,
    100_000, 1700000000, b'', bytes(32), bytes(8),
    10**9,
    wd,                         # 16 withdrawals_root
    0, 0,
    bytes(32), bytes(32), bytes(32),
]
if trunc == 'drop16':
    fields = fields[:16]
header_rlp = rlp.encode(fields)
with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(header_rlp)))
    f.write(header_rlp)
    pad = (-(8 + len(header_rlp))) % 8
    if pad: f.write(b'\x00' * pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_header_extract_block_roots.elf \
    -i "$in_file" -o "$out_file" -n 1000000 \
    >"$REPO_ROOT/gen-out/zisk_header_extract_block_roots_${name}.emu.log" 2>&1 || true

  local actual_status; actual_status="$(xxd -p -l 8 "$out_file" | tr -d '\n')"
  local exp_status_le; exp_status_le="$(python3 -c "print(int('$exp_status').to_bytes(8, 'little').hex())")"

  if [[ "$exp_status" == "0" ]]; then
    local actual_tx; actual_tx="$(dd if="$out_file" bs=1 skip=8 count=32 2>/dev/null | xxd -p | tr -d '\n')"
    local actual_rec; actual_rec="$(dd if="$out_file" bs=1 skip=40 count=32 2>/dev/null | xxd -p | tr -d '\n')"
    local actual_wd; actual_wd="$(dd if="$out_file" bs=1 skip=72 count=32 2>/dev/null | xxd -p | tr -d '\n')"
    if [[ "$actual_status" == "$exp_status_le" && "$actual_tx" == "$tx" && "$actual_rec" == "$rec" && "$actual_wd" == "$wd" ]]; then
      printf "  %-32s OK\n" "$name"
      return 0
    else
      printf "  %-32s FAIL  status=0x%s tx=%s rec=%s wd=%s\n" "$name" "$actual_status" "${actual_tx:0:8}.." "${actual_rec:0:8}.." "${actual_wd:0:8}.."
      return 1
    fi
  else
    if [[ "$actual_status" == "$exp_status_le" ]]; then
      printf "  %-32s OK   status=%d (rejected as expected)\n" "$name" "$exp_status"
      return 0
    else
      printf "  %-32s FAIL expected status=%d got 0x%s\n" "$name" "$exp_status" "$actual_status"
      return 1
    fi
  fi
}

A=$(printf '%.0s%s' {1..32} 'aa')
A="aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
B="bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"
C="cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc"
Z="0000000000000000000000000000000000000000000000000000000000000000"

FAILED=0
run_case "all_distinct"    "$A" "$B" "$C" || FAILED=1
run_case "all_zero"        "$Z" "$Z" "$Z" || FAILED=1
run_case "mixed"           "$A" "$Z" "$B" || FAILED=1
run_case "premerge_no_wd"  "$A" "$B" "$Z" drop16 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: header_extract_block_roots extracts transactions/receipt/withdrawals roots"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
