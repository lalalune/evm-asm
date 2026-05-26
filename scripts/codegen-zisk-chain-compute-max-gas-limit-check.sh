#!/usr/bin/env bash
# codegen-zisk-chain-compute-max-gas-limit-check.sh -- PR-K262.
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

echo "==> emit zisk_chain_compute_max_gas_limit ELF"
lake exe codegen --program zisk_chain_compute_max_gas_limit --halt linux93 \
  -o gen-out/zisk_chain_compute_max_gas_limit

REPO_ROOT="$(pwd)"

run_case() {
  local name="$1" gas_limits="$2" exp_status="$3" exp_max="$4"

  local in_file="$REPO_ROOT/gen-out/zisk_chain_compute_max_gas_limit_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_chain_compute_max_gas_limit_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys, rlp
def u_be(n):
    if n == 0: return b''
    return n.to_bytes((n.bit_length() + 7) // 8, 'big')

def make_header(gas_limit):
    return rlp.encode([
        b'\\xa1'*32, b'\\xa2'*32, b'\\xa3'*20, b'\\xa4'*32, b'\\xa5'*32,
        b'\\xa6'*32, b'\\x00'*256, b'', b'\\x01', u_be(gas_limit),
        b'', b'\\x83\\x01\\x02\\x03', b'', b'\\xa7'*32, b'\\x00'*8,
    ])

vals = $gas_limits
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

  "$ZISKEMU" -e gen-out/zisk_chain_compute_max_gas_limit.elf \
    -i "$in_file" -o "$out_file" -n 5000000 \
    >"$REPO_ROOT/gen-out/zisk_chain_compute_max_gas_limit_${name}.emu.log" 2>&1 || true

  local s_le; s_le="$(dd if="$out_file" bs=1 skip=8  count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local m_le; m_le="$(dd if="$out_file" bs=1 skip=16 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local status mx
  status="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$s_le'))[0])")"
  mx="$(    python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$m_le'))[0])")"

  if [[ "$status" == "$exp_status" && "$mx" == "$exp_max" ]]; then
    printf "  %-26s OK   status=%s max=%s\n" "$name" "$status" "$mx"
    return 0
  else
    printf "  %-26s FAIL status=%s/%s max=%s/%s\n" "$name" "$status" "$exp_status" "$mx" "$exp_max"
    return 1
  fi
}

FAILED=0
run_case "empty"        "[]"                              0 0        || FAILED=1
run_case "single_zero"  "[0]"                             0 0        || FAILED=1
run_case "single"       "[30000000]"                      0 30000000 || FAILED=1
run_case "three_inc"    "[10000000,20000000,30000000]"    0 30000000 || FAILED=1
run_case "three_mixed"  "[30000000,10000000,20000000]"    0 30000000 || FAILED=1
run_case "five_small"   "[5000,10000,7500,12500,8000]"    0 12500    || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: chain_compute_max_gas_limit finds max gas_limit across N headers"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
