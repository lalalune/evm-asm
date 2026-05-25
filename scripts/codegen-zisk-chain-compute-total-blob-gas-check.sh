#!/usr/bin/env bash
# codegen-zisk-chain-compute-total-blob-gas-check.sh -- PR-K231.
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

echo "==> emit zisk_chain_compute_total_blob_gas ELF"
lake exe codegen --program zisk_chain_compute_total_blob_gas --halt linux93 \
  -o gen-out/zisk_chain_compute_total_blob_gas

REPO_ROOT="$(pwd)"

run_case() {
  local name="$1" blob_gases="$2" exp_status="$3" exp_total="$4"

  local in_file="$REPO_ROOT/gen-out/zisk_chain_compute_total_blob_gas_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_chain_compute_total_blob_gas_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys, rlp
def u_be(n):
    if n == 0: return b''
    return n.to_bytes((n.bit_length() + 7) // 8, 'big')

def make_header_cancun(blob_gas_used):
    # 19 fields: ..., extra_data, prev_randao, nonce, base_fee_per_gas,
    # withdrawals_root, blob_gas_used (idx 17), excess_blob_gas (idx 18).
    return rlp.encode([
        b'\\xa1'*32, b'\\xa2'*32, b'\\xa3'*20, b'\\xa4'*32, b'\\xa5'*32,
        b'\\xa6'*32, b'\\x00'*256, b'', b'\\x01', b'\\x83\\xff\\xff\\xff',
        b'', b'\\x83\\x01\\x02\\x03', b'', b'\\xa7'*32, b'\\x00'*8,
        b'\\x82\\x01\\x00', b'\\xa8'*32,
        u_be(blob_gas_used),
        u_be(0),
    ])

gases = $blob_gases
headers = [make_header_cancun(g) for g in gases]
N = len(headers)
lengths = b''.join(struct.pack('<Q', len(h)) for h in headers)
flat = b''.join(headers)
with open(sys.argv[1], 'wb') as f:
    record = struct.pack('<Q', N) + lengths + flat
    f.write(record)
    pad = (-len(record)) % 8
    if pad: f.write(b'\x00' * pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_chain_compute_total_blob_gas.elf \
    -i "$in_file" -o "$out_file" -n 5000000 \
    >"$REPO_ROOT/gen-out/zisk_chain_compute_total_blob_gas_${name}.emu.log" 2>&1 || true

  local s_le; s_le="$(dd if="$out_file" bs=1 skip=8  count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local t_le; t_le="$(dd if="$out_file" bs=1 skip=16 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local status total
  status="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$s_le'))[0])")"
  total="$( python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$t_le'))[0])")"

  if [[ "$status" == "$exp_status" && "$total" == "$exp_total" ]]; then
    printf "  %-26s OK   status=%s total=%s\n" "$name" "$status" "$total"
    return 0
  else
    printf "  %-26s FAIL status=%s/%s total=%s/%s\n" "$name" "$status" "$exp_status" "$total" "$exp_total"
    return 1
  fi
}

FAILED=0
run_case "empty"          "[]"            0 0          || FAILED=1
run_case "single_zero"    "[0]"           0 0          || FAILED=1
run_case "single_some"    "[131072]"      0 131072     || FAILED=1
run_case "three_blocks"   "[131072,262144,393216]" 0 786432 || FAILED=1
run_case "mixed_zero"     "[0,131072,0]"  0 131072     || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: chain_compute_total_blob_gas sums blob_gas_used across N headers"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
