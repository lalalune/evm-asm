#!/usr/bin/env bash
# codegen-zisk-chain-validate-blob-gas-used-multiple-check.sh -- PR-K278.
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

echo "==> emit zisk_chain_validate_blob_gas_used_multiple ELF"
lake exe codegen --program zisk_chain_validate_blob_gas_used_multiple --halt linux93 \
  -o gen-out/zisk_chain_validate_blob_gas_used_multiple

REPO_ROOT="$(pwd)"

run_case() {
  local name="$1" vals="$2" exp_status="$3" exp_valid="$4" exp_bad_index="$5"

  local in_file="$REPO_ROOT/gen-out/zisk_chain_validate_blob_gas_used_multiple_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_chain_validate_blob_gas_used_multiple_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys, rlp
def u_be(n):
    if n == 0: return b''
    return n.to_bytes((n.bit_length() + 7) // 8, 'big')

def make_header(blob_gas_used):
    return rlp.encode([
        b'\\xa1'*32, b'\\xa2'*32, b'\\xa3'*20, b'\\xa4'*32, b'\\xa5'*32,
        b'\\xa6'*32, b'\\x00'*256, b'', b'\\x01', b'\\x83\\xff\\xff\\xff',
        b'', b'\\x83\\x01\\x02\\x03', b'', b'\\xa7'*32, b'\\x00'*8,
        b'\\x84\\x05\\xf5\\xe1\\x00', b'\\xa8'*32, u_be(blob_gas_used),
        b'', b'\\xa9'*32,
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

  "$ZISKEMU" -e gen-out/zisk_chain_validate_blob_gas_used_multiple.elf \
    -i "$in_file" -o "$out_file" -n 5000000 \
    >"$REPO_ROOT/gen-out/zisk_chain_validate_blob_gas_used_multiple_${name}.emu.log" 2>&1 || true

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

# GAS_PER_BLOB = 131072 = 0x20000
FAILED=0
run_case "empty"              "[]"                                  0 1 0 || FAILED=1
run_case "single_zero"        "[0]"                                 0 1 0 || FAILED=1
run_case "single_one_blob"    "[131072]"                            0 1 0 || FAILED=1
run_case "single_six_blob"    "[786432]"                            0 1 0 || FAILED=1
run_case "single_misaligned"  "[1]"                                 0 0 0 || FAILED=1
run_case "single_off_by_1"    "[131073]"                            0 0 0 || FAILED=1
run_case "three_all_aligned"  "[0, 131072, 262144]"                 0 1 0 || FAILED=1
run_case "three_bad_middle"   "[131072, 131071, 262144]"            0 0 1 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: chain_validate_blob_gas_used_multiple enforces GAS_PER_BLOB alignment"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
