#!/usr/bin/env bash
# codegen-zisk-tx-eip4844-compute-blob-gas-check.sh -- PR-K88.
#
# Decode an EIP-4844 inner RLP and compute blob_gas_used.
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

echo "==> emit zisk_tx_eip4844_compute_blob_gas ELF"
lake exe codegen --program zisk_tx_eip4844_compute_blob_gas --halt linux93 \
  -o gen-out/zisk_tx_eip4844_compute_blob_gas

REPO_ROOT="$(pwd)"

# run_case <name> <num_blobs> <gas_per_blob>
run_case() {
  local name="$1" n="$2" gpb="$3"

  local in_file="$REPO_ROOT/gen-out/zisk_tx_eip4844_compute_blob_gas_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_tx_eip4844_compute_blob_gas_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys, rlp
n = $n
gpb = $gpb
ALICE = bytes([0xaa] * 20)
R = bytes([0x11] * 32)
S = bytes([0x22] * 32)
H = bytes([0x01] + [0xab]*31)
inner = [
    1, 7, 10**9, 2*10**9, 21000,
    ALICE, 10**18, b'', [],
    1, [H]*n, 0,
    int.from_bytes(R, 'big'), int.from_bytes(S, 'big'),
]
inner_rlp = rlp.encode(inner)
with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(inner_rlp)))
    f.write(struct.pack('<Q', gpb))
    f.write(inner_rlp)
    pad = (-(16 + len(inner_rlp))) % 8
    if pad: f.write(b'\x00' * pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_tx_eip4844_compute_blob_gas.elf \
    -i "$in_file" -o "$out_file" -n 1000000 \
    >"$REPO_ROOT/gen-out/zisk_tx_eip4844_compute_blob_gas_${name}.emu.log" 2>&1 || true

  local expected=$((n * gpb))
  local actual_status; actual_status="$(xxd -p -l 8 "$out_file" | tr -d '\n')"
  local actual_blob_gas; actual_blob_gas="$(dd if="$out_file" bs=1 skip=8 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local exp_blob_gas_le; exp_blob_gas_le="$(python3 -c "print(int('$expected').to_bytes(8, 'little').hex())")"

  if [[ "$actual_status" == "0000000000000000" && "$actual_blob_gas" == "$exp_blob_gas_le" ]]; then
    printf "  %-30s OK   n=%d blob_gas=%d\n" "$name" "$n" "$expected"
    return 0
  else
    printf "  %-30s FAIL  status=0x%s blob_gas=0x%s (expected %d)\n" "$name" "$actual_status" "$actual_blob_gas" "$expected"
    return 1
  fi
}

GAS_PER_BLOB=131072

FAILED=0
run_case "one_blob"       1 "$GAS_PER_BLOB"  || FAILED=1
run_case "three_blobs"    3 "$GAS_PER_BLOB"  || FAILED=1
run_case "six_blobs"      6 "$GAS_PER_BLOB"  || FAILED=1
run_case "nine_blobs"     9 "$GAS_PER_BLOB"  || FAILED=1
# Different gas_per_blob
run_case "one_blob_custom_gas" 1 100  || FAILED=1
run_case "two_blobs_big_gas"   2 1000000  || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: tx_eip4844_compute_blob_gas matches count × gas_per_blob"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
