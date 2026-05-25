#!/usr/bin/env bash
# codegen-zisk-chain-compute-min-gas-used-check.sh -- PR-K238.
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

echo "==> emit zisk_chain_compute_min_gas_used ELF"
lake exe codegen --program zisk_chain_compute_min_gas_used --halt linux93 \
  -o gen-out/zisk_chain_compute_min_gas_used

REPO_ROOT="$(pwd)"

run_case() {
  local name="$1" gas_useds="$2" exp_status="$3" exp_min="$4"

  local in_file="$REPO_ROOT/gen-out/zisk_chain_compute_min_gas_used_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_chain_compute_min_gas_used_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys, rlp
def u_be(n):
    if n == 0: return b''
    return n.to_bytes((n.bit_length() + 7) // 8, 'big')

def make_header(gas_used):
    return rlp.encode([
        b'\\xa1'*32, b'\\xa2'*32, b'\\xa3'*20, b'\\xa4'*32, b'\\xa5'*32,
        b'\\xa6'*32, b'\\x00'*256, b'', b'\\x01', b'\\x83\\xff\\xff\\xff',
        u_be(gas_used), b'\\x83\\x01\\x02\\x03', b'', b'\\xa7'*32,
        b'\\x00'*8, b'\\x82\\x01\\x00',
    ])

vals = $gas_useds
headers = [make_header(v) for v in vals]
N = len(headers)
lengths = b''.join(struct.pack('<Q', len(h)) for h in headers)
flat = b''.join(headers)
with open(sys.argv[1], 'wb') as f:
    record = struct.pack('<Q', N) + lengths + flat
    f.write(record)
    pad = (-len(record)) % 8
    if pad: f.write(b'\x00' * pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_chain_compute_min_gas_used.elf \
    -i "$in_file" -o "$out_file" -n 5000000 \
    >"$REPO_ROOT/gen-out/zisk_chain_compute_min_gas_used_${name}.emu.log" 2>&1 || true

  local s_le; s_le="$(dd if="$out_file" bs=1 skip=8  count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local m_le; m_le="$(dd if="$out_file" bs=1 skip=16 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local status mn
  status="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$s_le'))[0])")"
  mn="$(    python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$m_le'))[0])")"

  if [[ "$status" == "$exp_status" && "$mn" == "$exp_min" ]]; then
    printf "  %-26s OK   status=%s min=%s\n" "$name" "$status" "$mn"
    return 0
  else
    printf "  %-26s FAIL status=%s/%s min=%s/%s\n" "$name" "$status" "$exp_status" "$mn" "$exp_min"
    return 1
  fi
}

FAILED=0
run_case "empty"          "[]"                       0 0           || FAILED=1
run_case "single_zero"    "[0]"                      0 0           || FAILED=1
run_case "single_some"    "[21000]"                  0 21000       || FAILED=1
run_case "increasing"     "[10000,20000,30000]"      0 10000       || FAILED=1
run_case "decreasing"     "[30000,20000,10000]"      0 10000       || FAILED=1
run_case "low_in_middle"  "[20000,5000,30000]"       0 5000        || FAILED=1
run_case "all_equal"      "[15000,15000,15000]"      0 15000       || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: chain_compute_min_gas_used returns min(header.gas_used) across N"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
