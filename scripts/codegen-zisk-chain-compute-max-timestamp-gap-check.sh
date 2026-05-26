#!/usr/bin/env bash
# codegen-zisk-chain-compute-max-timestamp-gap-check.sh -- PR-K279.
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

echo "==> emit zisk_chain_compute_max_timestamp_gap ELF"
lake exe codegen --program zisk_chain_compute_max_timestamp_gap --halt linux93 \
  -o gen-out/zisk_chain_compute_max_timestamp_gap

REPO_ROOT="$(pwd)"

run_case() {
  local name="$1" vals="$2" exp_status="$3" exp_gap="$4" exp_bad="$5"

  local in_file="$REPO_ROOT/gen-out/zisk_chain_compute_max_timestamp_gap_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_chain_compute_max_timestamp_gap_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys, rlp
def u_be(n):
    if n == 0: return b''
    return n.to_bytes((n.bit_length() + 7) // 8, 'big')

def make_header(ts):
    return rlp.encode([
        b'\\xa1'*32, b'\\xa2'*32, b'\\xa3'*20, b'\\xa4'*32, b'\\xa5'*32,
        b'\\xa6'*32, b'\\x00'*256, b'', b'\\x01', b'\\x83\\xff\\xff\\xff',
        b'', u_be(ts), b'', b'\\xa7'*32, b'\\x00'*8,
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

  "$ZISKEMU" -e gen-out/zisk_chain_compute_max_timestamp_gap.elf \
    -i "$in_file" -o "$out_file" -n 5000000 \
    >"$REPO_ROOT/gen-out/zisk_chain_compute_max_timestamp_gap_${name}.emu.log" 2>&1 || true

  local s_le; s_le="$(dd if="$out_file" bs=1 skip=0  count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local g_le; g_le="$(dd if="$out_file" bs=1 skip=8  count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local b_le; b_le="$(dd if="$out_file" bs=1 skip=16 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local status gap bad
  status="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$s_le'))[0])")"
  gap="$(   python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$g_le'))[0])")"
  bad="$(   python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$b_le'))[0])")"

  if [[ "$status" == "$exp_status" && "$gap" == "$exp_gap" && "$bad" == "$exp_bad" ]]; then
    printf "  %-32s OK   status=%s gap=%s bad=%s\n" "$name" "$status" "$gap" "$bad"
    return 0
  else
    printf "  %-32s FAIL status=%s/%s gap=%s/%s bad=%s/%s\n" "$name" "$status" "$exp_status" "$gap" "$exp_gap" "$bad" "$exp_bad"
    return 1
  fi
}

FAILED=0
run_case "empty"                "[]"                            0 0  0 || FAILED=1
run_case "single"               "[100]"                         0 0  0 || FAILED=1
run_case "two_equal"            "[100, 100]"                    0 0  0 || FAILED=1
run_case "two_inc"              "[100, 150]"                    0 50 0 || FAILED=1
run_case "three_uniform"        "[100, 112, 124]"               0 12 0 || FAILED=1
run_case "three_varying"        "[100, 112, 150]"               0 38 0 || FAILED=1
run_case "five_peak_at_3"       "[100, 105, 110, 200, 210]"     0 90 0 || FAILED=1
run_case "two_dec_fail"         "[200, 100]"                    3 0  1 || FAILED=1
run_case "three_dec_at_2"       "[100, 120, 110]"               3 20 2 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: chain_compute_max_timestamp_gap finds longest gap"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
