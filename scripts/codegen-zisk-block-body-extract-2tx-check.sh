#!/usr/bin/env bash
# codegen-zisk-block-body-extract-2tx-check.sh -- PR-K177.
#
# Body-side primitive: parses a 3-field body, asserts exactly two
# transactions + empty ommers, and returns (tx0 off+len, tx1 off+len)
# in body-relative coordinates so callers can feed K171/K176 etc.
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

echo "==> emit zisk_block_body_extract_2tx ELF"
lake exe codegen --program zisk_block_body_extract_2tx --halt linux93 \
  -o gen-out/zisk_block_body_extract_2tx

REPO_ROOT="$(pwd)"

# run_case <name> <body_build_expr_py>
#   <exp_status> <exp_tx0_off> <exp_tx0_len> <exp_tx1_off> <exp_tx1_len>
run_case() {
  local name="$1" body_expr="$2"
  local exp_status="$3" exp_t0o="$4" exp_t0l="$5" exp_t1o="$6" exp_t1l="$7"

  local in_file="$REPO_ROOT/gen-out/zisk_block_body_extract_2tx_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_block_body_extract_2tx_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys, rlp
body_rlp = $body_expr
with open(sys.argv[1], 'wb') as f:
    record = struct.pack('<Q', len(body_rlp)) + body_rlp
    f.write(record)
    pad = (-len(record)) % 8
    if pad: f.write(b'\x00' * pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_block_body_extract_2tx.elf \
    -i "$in_file" -o "$out_file" -n 5000000 \
    >"$REPO_ROOT/gen-out/zisk_block_body_extract_2tx_${name}.emu.log" 2>&1 || true

  local status_le; status_le="$(xxd -p -l 8 "$out_file" | tr -d '\n')"
  local t0o_le;    t0o_le="$(   dd if="$out_file" bs=1 skip=8  count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local t0l_le;    t0l_le="$(   dd if="$out_file" bs=1 skip=16 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local t1o_le;    t1o_le="$(   dd if="$out_file" bs=1 skip=24 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local t1l_le;    t1l_le="$(   dd if="$out_file" bs=1 skip=32 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local status t0o t0l t1o t1l
  status="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$status_le'))[0])")"
  t0o="$(   python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$t0o_le'))[0])")"
  t0l="$(   python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$t0l_le'))[0])")"
  t1o="$(   python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$t1o_le'))[0])")"
  t1l="$(   python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$t1l_le'))[0])")"

  if [[ "$status" == "$exp_status" && "$t0o" == "$exp_t0o" && "$t0l" == "$exp_t0l" \
        && "$t1o" == "$exp_t1o" && "$t1l" == "$exp_t1l" ]]; then
    printf "  %-26s OK   status=%s tx0=(%s,%s) tx1=(%s,%s)\n" \
      "$name" "$status" "$t0o" "$t0l" "$t1o" "$t1l"
    return 0
  else
    printf "  %-26s FAIL status=%s/exp%s tx0=(%s,%s)/exp(%s,%s) tx1=(%s,%s)/exp(%s,%s)\n" \
      "$name" "$status" "$exp_status" \
      "$t0o" "$t0l" "$exp_t0o" "$exp_t0l" \
      "$t1o" "$t1l" "$exp_t1o" "$exp_t1l"
    return 1
  fi
}

# Compute the precise (offset, length) of each tx item using rlp's
# decoder is awkward without partial decoding; use Python to construct
# the body and report the expected offsets manually.
compute_2tx_body() {
  local tx0_hex="$1" tx1_hex="$2"
  uv run --directory execution-specs --quiet python3 -c "
import struct, sys, rlp
tx0 = bytes.fromhex('$tx0_hex')
tx1 = bytes.fromhex('$tx1_hex')
body = rlp.encode([[tx0, tx1], [], []])

# Figure out the offsets of tx0/tx1 inside the body by walking the
# outer list prefix manually.
def list_prefix_size(first_byte):
    if first_byte < 0xf8:
        return 1
    return 1 + (first_byte - 0xf7)

def item_prefix_size(first_byte):
    # Walk past a single RLP item starting at first_byte, returning the
    # total prefix length (NOT including content).
    if first_byte < 0x80:
        return 0
    if first_byte < 0xb8:
        return 1
    if first_byte < 0xc0:
        return 1 + (first_byte - 0xb7)
    if first_byte < 0xf8:
        return 1
    return 1 + (first_byte - 0xf7)

def decode_len(b):
    # Return (item_total_len, content_offset_from_start).
    f = b[0]
    if f < 0x80:
        return 1, 0
    if f < 0xb8:
        return 1 + (f - 0x80), 1
    if f < 0xc0:
        lol = f - 0xb7
        ll = int.from_bytes(b[1:1+lol], 'big')
        return 1 + lol + ll, 1 + lol
    if f < 0xf8:
        return 1 + (f - 0xc0), 1
    lol = f - 0xf7
    ll = int.from_bytes(b[1:1+lol], 'big')
    return 1 + lol + ll, 1 + lol

# Outer body list
outer_total, outer_content_off = decode_len(body)
# Inner txs list (first item of the body)
txs_start = outer_content_off
txs_total, txs_content_off = decode_len(body[txs_start:])
# tx0 sits at txs_start + txs_content_off
tx0_start_in_body = txs_start + txs_content_off
tx0_total, _ = decode_len(body[tx0_start_in_body:])
# For our case, tx0 is a byte-string (legacy tx); the FULL encoded item
# (prefix + content) is what K20 returns for byte-string items? NO -- per
# K20's doc: byte-strings have their prefix STRIPPED.
# For a byte-string item, K20 returns (item_start + prefix_len,
# item_content_len). For list items it returns (item_start, full_len).
def k20_offlen(b, item_start_in_body):
    f = b[item_start_in_body]
    total, content_off = decode_len(b[item_start_in_body:])
    if f < 0xc0:
        # byte-string: strip prefix
        return item_start_in_body + content_off, total - content_off
    else:
        # list: keep prefix
        return item_start_in_body, total

tx0_off, tx0_len = k20_offlen(body, tx0_start_in_body)
tx1_start_in_body = tx0_start_in_body + tx0_total
tx1_off, tx1_len = k20_offlen(body, tx1_start_in_body)
print(f'body_hex={body.hex()}')
print(f'tx0_off={tx0_off} tx0_len={tx0_len}')
print(f'tx1_off={tx1_off} tx1_len={tx1_len}')
"
}

TX_A="f8500184ee6b280082520894aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa881bc16d674ec80000801ba01111111111111111111111111111111111111111111111111111111111111111a02222222222222222222222222222222222222222222222222222222222222222"
TX_B="f8500284ee6b280082520894bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb881bc16d674ec80000801ba03333333333333333333333333333333333333333333333333333333333333333a04444444444444444444444444444444444444444444444444444444444444444"

# Precompute the expected offsets and stash them in /tmp.
compute_2tx_body "$TX_A" "$TX_B" > /tmp/k177_compute.txt
tx0_off=$(grep -oP 'tx0_off=\K[0-9]+' /tmp/k177_compute.txt)
tx0_len=$(grep -oP 'tx0_len=\K[0-9]+' /tmp/k177_compute.txt)
tx1_off=$(grep -oP 'tx1_off=\K[0-9]+' /tmp/k177_compute.txt)
tx1_len=$(grep -oP 'tx1_len=\K[0-9]+' /tmp/k177_compute.txt)
echo "  precomputed: tx0=($tx0_off,$tx0_len) tx1=($tx1_off,$tx1_len)"

FAILED=0
# Standard 2-tx body, ommers empty
run_case "two_legacy" "rlp.encode([[bytes.fromhex('$TX_A'), bytes.fromhex('$TX_B')], [], []])" \
   0 "$tx0_off" "$tx0_len" "$tx1_off" "$tx1_len" || FAILED=1

# 3-tx body -> count_fail
run_case "fail_three_txs" \
  "rlp.encode([[bytes.fromhex('$TX_A'), bytes.fromhex('$TX_B'), bytes.fromhex('$TX_A')], [], []])" \
   3 0 0 0 0 || FAILED=1
# 1-tx body -> count_fail
run_case "fail_one_tx" \
  "rlp.encode([[bytes.fromhex('$TX_A')], [], []])" 3 0 0 0 0 || FAILED=1
# Ommers non-empty -> ommers_fail
run_case "fail_nonempty_ommers" \
  "rlp.encode([[bytes.fromhex('$TX_A'), bytes.fromhex('$TX_B')], [bytes.fromhex('$TX_A')], []])" \
   2 0 0 0 0 || FAILED=1
# 2-item body (no withdrawals) -> parse_fail (block_body_decode expects 3 fields)
run_case "fail_two_field_body" \
  "rlp.encode([[bytes.fromhex('$TX_A'), bytes.fromhex('$TX_B')], []])" 1 0 0 0 0 || FAILED=1
# Garbage body -> parse_fail
run_case "fail_garbage_body" "b'\\x00'" 1 0 0 0 0 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: block_body_extract_2tx returns correct (off,len) pairs and rejects misshaped bodies"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
