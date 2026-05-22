#!/usr/bin/env bash
# codegen-zisk-block-validate-blob-gas-max-cap-check.sh -- PR-K93.
#
# Cancun cap: header.blob_gas_used <= MAX_BLOB_GAS_PER_BLOCK.
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

echo "==> emit zisk_block_validate_blob_gas_max_cap ELF"
lake exe codegen --program zisk_block_validate_blob_gas_max_cap --halt linux93 \
  -o gen-out/zisk_block_validate_blob_gas_max_cap

REPO_ROOT="$(pwd)"

# run_case <name> <bgu> <max_blobs> <gas_per_blob> <expected_status>
run_case() {
  local name="$1" bgu="$2" maxb="$3" gpb="$4" exp="$5"

  local in_file="$REPO_ROOT/gen-out/zisk_block_validate_blob_gas_max_cap_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_block_validate_blob_gas_max_cap_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys, rlp
bgu = $bgu
fields = [
    bytes(32), bytes(32), bytes(20), bytes(32), bytes(32),
    bytes(32), bytes(256), 0, 1, 30_000_000,
    100_000, 1700000000, b'', bytes(32), bytes(8),
    10**9, bytes(32),
    bgu,                        # 17 blob_gas_used
    0,                          # 18 excess_blob_gas
    bytes(32), bytes(32), bytes(32),
]
header_rlp = rlp.encode(fields)
with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(header_rlp)))
    f.write(struct.pack('<Q', $maxb))
    f.write(struct.pack('<Q', $gpb))
    f.write(header_rlp)
    pad = (-(24 + len(header_rlp))) % 8
    if pad: f.write(b'\x00' * pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_block_validate_blob_gas_max_cap.elf \
    -i "$in_file" -o "$out_file" -n 1000000 \
    >"$REPO_ROOT/gen-out/zisk_block_validate_blob_gas_max_cap_${name}.emu.log" 2>&1 || true

  local actual_status; actual_status="$(xxd -p -l 8 "$out_file" | tr -d '\n')"
  local exp_status_le; exp_status_le="$(python3 -c "print(int('$exp').to_bytes(8, 'little').hex())")"

  if [[ "$actual_status" == "$exp_status_le" ]]; then
    printf "  %-32s OK   status=%d\n" "$name" "$exp"
    return 0
  else
    printf "  %-32s FAIL status=0x%s expected=%d\n" "$name" "$actual_status" "$exp"
    return 1
  fi
}

MAX_BLOBS=21
GPB=131072
# MAX_BLOB_GAS_PER_BLOCK = 21 * 131072 = 2752512

FAILED=0
# Within cap
run_case "zero"                  0       "$MAX_BLOBS" "$GPB" 0 || FAILED=1
run_case "one_blob"              131072  "$MAX_BLOBS" "$GPB" 0 || FAILED=1
run_case "half_cap"              1376256 "$MAX_BLOBS" "$GPB" 0 || FAILED=1
run_case "exactly_cap"           2752512 "$MAX_BLOBS" "$GPB" 0 || FAILED=1
run_case "twenty_blobs"          2621440 "$MAX_BLOBS" "$GPB" 0 || FAILED=1
# Over cap
run_case "one_past_cap"          2752513 "$MAX_BLOBS" "$GPB" 3 || FAILED=1
run_case "twentytwo_blobs"       2883584 "$MAX_BLOBS" "$GPB" 3 || FAILED=1
# Overflow (max_blobs * gas_per_blob exceeds u64)
MAX_U64=18446744073709551615
run_case "overflow_args"         0       "$MAX_U64"   2     2 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: block_validate_blob_gas_max_cap enforces MAX_BLOB_GAS_PER_BLOCK"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
