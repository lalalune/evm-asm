#!/usr/bin/env bash
# codegen-zisk-header-compute-summary-struct-check.sh -- PR-K214.
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

echo "==> emit zisk_header_compute_summary_struct ELF"
lake exe codegen --program zisk_header_compute_summary_struct --halt linux93 \
  -o gen-out/zisk_header_compute_summary_struct

REPO_ROOT="$(pwd)"

run_case() {
  local name="$1" number="$2" timestamp="$3" gas_used="$4" base_fee="$5"

  local in_file="$REPO_ROOT/gen-out/zisk_header_compute_summary_struct_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_header_compute_summary_struct_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_header_compute_summary_struct_${name}.expected.txt"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys, rlp
try:
    from Crypto.Hash import keccak
    def keccak256(b):
        h = keccak.new(digest_bits=256); h.update(b); return h.digest()
except Exception:
    import sha3
    def keccak256(b): return sha3.keccak_256(b).digest()

def u_be(n):
    if n == 0: return b''
    return n.to_bytes((n.bit_length() + 7) // 8, 'big')

num, ts, gu, bf = $number, $timestamp, $gas_used, $base_fee
state_root = b'\\xa4'*32
fields = [
    b'\\xa1'*32, b'\\xa2'*32, b'\\xa3'*20, state_root, b'\\xa5'*32,
    b'\\xa6'*32, b'\\x00'*256, b'', u_be(num), b'\\x83\\xff\\xff\\xff',
    u_be(gu), u_be(ts), b'', b'\\xa7'*32, b'\\x00'*8,
    u_be(bf),
]
header_rlp = rlp.encode(fields)
hash = keccak256(header_rlp)
with open(sys.argv[1], 'wb') as f:
    record = struct.pack('<Q', len(header_rlp)) + header_rlp
    f.write(record)
    pad = (-len(record)) % 8
    if pad: f.write(b'\x00' * pad)
with open(sys.argv[2], 'w') as f:
    f.write(hash.hex() + ',' + state_root.hex())
" "$in_file" "$exp_file"

  "$ZISKEMU" -e gen-out/zisk_header_compute_summary_struct.elf \
    -i "$in_file" -o "$out_file" -n 2000000 \
    >"$REPO_ROOT/gen-out/zisk_header_compute_summary_struct_${name}.emu.log" 2>&1 || true

  local status_le; status_le="$(xxd -p -l 8 "$out_file" | tr -d '\n')"
  local actual_hash; actual_hash="$(dd if="$out_file" bs=1 skip=8 count=32 2>/dev/null | xxd -p | tr -d '\n')"
  local actual_sr; actual_sr="$(dd if="$out_file" bs=1 skip=40 count=32 2>/dev/null | xxd -p | tr -d '\n')"
  local actual_num_le; actual_num_le="$(dd if="$out_file" bs=1 skip=72 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local actual_ts_le;  actual_ts_le="$( dd if="$out_file" bs=1 skip=80 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local actual_gu_le;  actual_gu_le="$( dd if="$out_file" bs=1 skip=88 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local actual_bf_le;  actual_bf_le="$( dd if="$out_file" bs=1 skip=96 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local actual_num actual_ts actual_gu actual_bf
  actual_num="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$actual_num_le'))[0])")"
  actual_ts="$( python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$actual_ts_le'))[0])")"
  actual_gu="$( python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$actual_gu_le'))[0])")"
  actual_bf="$( python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$actual_bf_le'))[0])")"
  local exp_hash="$(cut -d, -f1 "$exp_file")"
  local exp_sr="$(cut -d, -f2 "$exp_file")"

  if [[ "$actual_hash" == "$exp_hash" && "$actual_sr" == "$exp_sr" \
        && "$actual_num" == "$number" && "$actual_ts" == "$timestamp" \
        && "$actual_gu" == "$gas_used" && "$actual_bf" == "$base_fee" ]]; then
    printf "  %-26s OK   hash=%s... num=%s ts=%s gu=%s bf=%s\n" "$name" "${actual_hash:0:16}" "$actual_num" "$actual_ts" "$actual_gu" "$actual_bf"
    return 0
  else
    printf "  %-26s FAIL\n" "$name"
    printf "      hash=%s/exp%s\n" "$actual_hash" "$exp_hash"
    printf "      sr=%s/exp%s\n" "$actual_sr" "$exp_sr"
    printf "      num=%s/%s ts=%s/%s gu=%s/%s bf=%s/%s\n" "$actual_num" "$number" "$actual_ts" "$timestamp" "$actual_gu" "$gas_used" "$actual_bf" "$base_fee"
    return 1
  fi
}

FAILED=0
run_case "typical_block"  18000000 1700000000 25000000 30000000000 || FAILED=1
run_case "small_numbers"  1        100        21000    7           || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: header_compute_summary_struct returns full 96B summary"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
