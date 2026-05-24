#!/usr/bin/env bash
# codegen-zisk-block-body-extract-1tx-check.sh -- PR-K188.
#
# Body-side primitive for 1-tx blocks.
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

echo "==> emit zisk_block_body_extract_1tx ELF"
lake exe codegen --program zisk_block_body_extract_1tx --halt linux93 \
  -o gen-out/zisk_block_body_extract_1tx

REPO_ROOT="$(pwd)"

# run_case <name> <body_build_py> <exp_status> <exp_tx0_off> <exp_tx0_len>
run_case() {
  local name="$1" body_expr="$2" exp_status="$3" exp_t0o="$4" exp_t0l="$5"

  local in_file="$REPO_ROOT/gen-out/zisk_block_body_extract_1tx_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_block_body_extract_1tx_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys, rlp
body_rlp = $body_expr
with open(sys.argv[1], 'wb') as f:
    record = struct.pack('<Q', len(body_rlp)) + body_rlp
    f.write(record)
    pad = (-len(record)) % 8
    if pad: f.write(b'\x00' * pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_block_body_extract_1tx.elf \
    -i "$in_file" -o "$out_file" -n 2000000 \
    >"$REPO_ROOT/gen-out/zisk_block_body_extract_1tx_${name}.emu.log" 2>&1 || true

  local status_le; status_le="$(xxd -p -l 8 "$out_file" | tr -d '\n')"
  local t0o_le;    t0o_le="$(   dd if="$out_file" bs=1 skip=8  count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local t0l_le;    t0l_le="$(   dd if="$out_file" bs=1 skip=16 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local status t0o t0l
  status="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$status_le'))[0])")"
  t0o="$(   python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$t0o_le'))[0])")"
  t0l="$(   python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$t0l_le'))[0])")"

  if [[ "$status" == "$exp_status" && "$t0o" == "$exp_t0o" && "$t0l" == "$exp_t0l" ]]; then
    printf "  %-26s OK   status=%s tx0=(%s,%s)\n" "$name" "$status" "$t0o" "$t0l"
    return 0
  else
    printf "  %-26s FAIL status=%s/%s tx0=(%s,%s)/(%s,%s)\n" \
      "$name" "$status" "$exp_status" "$t0o" "$t0l" "$exp_t0o" "$exp_t0l"
    return 1
  fi
}

TX_A="f8500184ee6b280082520894aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa881bc16d674ec80000801ba01111111111111111111111111111111111111111111111111111111111111111a02222222222222222222222222222222222222222222222222222222222222222"

# Compute expected tx0 offset/len in the body for the single legacy tx.
# Body = rlp([[tx0], [], []])
# - outer prefix: 1 byte (short list) OR 2..3 bytes for long
# - inner txs list prefix: 1..3 bytes
# For our 109-byte tx0: inner txs list = 1 + (1 + 109) = 111 bytes total
#   inner_prefix = 1 byte (since 110 fits in short-list? 110 > 55, so long-list 2 bytes)
# Actually: txs payload = tx0 wrapped = (rlp_prefix_for_tx_string) + tx0_bytes
# But tx0 is already wire-format -- it gets re-wrapped as a byte-string by rlp.encode([tx0,...])
# For tx0 of len 109 (>55), wrap = 0xb8 0x6d + 109 bytes = 111 bytes total
# txs list payload = 111 bytes -> long-list, prefix = 0xf8 0x6f (2 bytes)
# Total txs list = 113 bytes
# ommers + withdrawals: 0xc0 0xc0 (2 bytes)
# body payload = 115 bytes -> long-list, prefix = 0xf8 0x73 (2 bytes)
# Total body = 117 bytes
# tx0 wrapped string starts at offset 2+2 = 4 (outer prefix + txs prefix)
# K20 returns content offset for byte-string items: 4 + 2 (tx0 prefix) = 6
# K20 returns content length: 109
EXPECTED_OFF=6
EXPECTED_LEN=109

FAILED=0
run_case "one_legacy" "rlp.encode([[bytes.fromhex('$TX_A')], [], []])" 0 $EXPECTED_OFF $EXPECTED_LEN || FAILED=1
run_case "fail_two_txs" \
  "rlp.encode([[bytes.fromhex('$TX_A'), bytes.fromhex('$TX_A')], [], []])" 3 0 0 || FAILED=1
run_case "fail_zero_txs" \
  "rlp.encode([[], [], []])" 3 0 0 || FAILED=1
run_case "fail_nonempty_ommers" \
  "rlp.encode([[bytes.fromhex('$TX_A')], [bytes.fromhex('$TX_A')], []])" 2 0 0 || FAILED=1
run_case "fail_two_field_body" \
  "rlp.encode([[bytes.fromhex('$TX_A')], []])" 1 0 0 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: block_body_extract_1tx returns correct (off,len) and rejects misshaped bodies"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
