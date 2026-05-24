#!/usr/bin/env bash
# codegen-zisk-chain-compute-total-gas-used-check.sh -- PR-K196.
#
# Sum header.gas_used across an N-header chain.
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

echo "==> emit zisk_chain_compute_total_gas_used ELF"
lake exe codegen --program zisk_chain_compute_total_gas_used --halt linux93 \
  -o gen-out/zisk_chain_compute_total_gas_used

REPO_ROOT="$(pwd)"

# run_case <name> <gas_used_list_py> <exp_status> <exp_sum>
run_case() {
  local name="$1" gus="$2" exp_status="$3" exp_sum="$4"

  local in_file="$REPO_ROOT/gen-out/zisk_chain_compute_total_gas_used_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_chain_compute_total_gas_used_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys, rlp

def u_be(n):
    if n == 0: return b''
    return n.to_bytes((n.bit_length() + 7) // 8, 'big')

def make_header(gas_used):
    return rlp.encode([
        b'\\xa1'*32, b'\\xa2'*32, b'\\xa3'*20, b'\\xa4'*32, b'\\xa5'*32,
        b'\\xa6'*32, b'\\x00'*256, b'', b'\\x01', b'\\x83\\xff\\xff\\xff',
        u_be(gas_used), b'\\x83\\x01\\x02\\x03', b'', b'\\xa7'*32, b'\\x00'*8,
    ])

gus = $gus  # list of gas_used per header
headers = [make_header(g) for g in gus]
N = len(headers)
lengths = b''.join(struct.pack('<Q', len(h)) for h in headers)
flat = b''.join(headers)

with open(sys.argv[1], 'wb') as f:
    record = struct.pack('<Q', N) + lengths + flat
    f.write(record)
    pad = (-len(record)) % 8
    if pad: f.write(b'\x00' * pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_chain_compute_total_gas_used.elf \
    -i "$in_file" -o "$out_file" -n 5000000 \
    >"$REPO_ROOT/gen-out/zisk_chain_compute_total_gas_used_${name}.emu.log" 2>&1 || true

  local status_le; status_le="$(xxd -p -l 8 "$out_file" | tr -d '\n')"
  local sum_le;    sum_le="$(   dd if="$out_file" bs=1 skip=8 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local status sum
  status="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$status_le'))[0])")"
  sum="$(   python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$sum_le'))[0])")"

  if [[ "$status" == "$exp_status" && "$sum" == "$exp_sum" ]]; then
    printf "  %-28s OK   status=%s sum=%s\n" "$name" "$status" "$sum"
    return 0
  else
    printf "  %-28s FAIL status=%s/%s sum=%s/%s\n" \
      "$name" "$status" "$exp_status" "$sum" "$exp_sum"
    return 1
  fi
}

FAILED=0
run_case "empty_chain"      "[]"                  0 0       || FAILED=1
run_case "single_block"     "[21000]"             0 21000   || FAILED=1
run_case "three_blocks"     "[21000, 50000, 30000]" 0 101000 || FAILED=1
run_case "five_blocks_big"  "[1000000, 2000000, 3000000, 4000000, 5000000]" 0 15000000 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: chain_compute_total_gas_used aggregates header.gas_used correctly"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
