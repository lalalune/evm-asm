#!/usr/bin/env bash
# codegen-zisk-chain-validate-excess-blob-gas-non-increasing-check.sh -- PR-K275.
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

echo "==> emit zisk_chain_validate_excess_blob_gas_non_increasing ELF"
lake exe codegen --program zisk_chain_validate_excess_blob_gas_non_increasing --halt linux93 \
  -o gen-out/zisk_chain_validate_excess_blob_gas_non_increasing

REPO_ROOT="$(pwd)"

run_case() {
  local name="$1" vals="$2" exp_status="$3" exp_valid="$4" exp_bad_index="$5"

  local in_file="$REPO_ROOT/gen-out/zisk_chain_validate_excess_blob_gas_non_increasing_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_chain_validate_excess_blob_gas_non_increasing_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys, rlp
def u_be(n):
    if n == 0: return b''
    return n.to_bytes((n.bit_length() + 7) // 8, 'big')

def make_header(excess_blob_gas):
    return rlp.encode([
        b'\\xa1'*32, b'\\xa2'*32, b'\\xa3'*20, b'\\xa4'*32, b'\\xa5'*32,
        b'\\xa6'*32, b'\\x00'*256, b'', b'\\x01', b'\\x83\\xff\\xff\\xff',
        b'', b'\\x83\\x01\\x02\\x03', b'', b'\\xa7'*32, b'\\x00'*8,
        b'\\x84\\x05\\xf5\\xe1\\x00', b'\\xa8'*32, b'',
        u_be(excess_blob_gas), b'\\xa9'*32,
    ])

vals = $vals
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

  "$ZISKEMU" -e gen-out/zisk_chain_validate_excess_blob_gas_non_increasing.elf \
    -i "$in_file" -o "$out_file" -n 5000000 \
    >"$REPO_ROOT/gen-out/zisk_chain_validate_excess_blob_gas_non_increasing_${name}.emu.log" 2>&1 || true

  local s_le; s_le="$(dd if="$out_file" bs=1 skip=0  count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local v_le; v_le="$(dd if="$out_file" bs=1 skip=8  count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local b_le; b_le="$(dd if="$out_file" bs=1 skip=16 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local status valid bad_index
  status="$(   python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$s_le'))[0])")"
  valid="$(    python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$v_le'))[0])")"
  bad_index="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$b_le'))[0])")"

  if [[ "$status" == "$exp_status" && "$valid" == "$exp_valid" && "$bad_index" == "$exp_bad_index" ]]; then
    printf "  %-32s OK   status=%s valid=%s bad_index=%s\n" "$name" "$status" "$valid" "$bad_index"
    return 0
  else
    printf "  %-32s FAIL status=%s/%s valid=%s/%s bad_index=%s/%s\n" "$name" "$status" "$exp_status" "$valid" "$exp_valid" "$bad_index" "$exp_bad_index"
    return 1
  fi
}

FAILED=0
run_case "empty"                  "[]"                              0 1 0 || FAILED=1
run_case "single"                 "[7864320]"                       0 1 0 || FAILED=1
run_case "two_equal"              "[100, 100]"                      0 1 0 || FAILED=1
run_case "two_dec"                "[200, 100]"                      0 1 0 || FAILED=1
run_case "two_inc"                "[100, 200]"                      0 0 1 || FAILED=1
run_case "three_non_increasing"   "[3, 2, 2]"                       0 1 0 || FAILED=1
run_case "three_bump_at_2"        "[3, 2, 5]"                       0 0 2 || FAILED=1
run_case "five_bump_at_3"         "[5, 4, 3, 4, 1]"                 0 0 3 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: chain_validate_excess_blob_gas_non_increasing predicate matches"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
