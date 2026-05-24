#!/usr/bin/env bash
# codegen-zisk-block-body-summary-check.sh -- PR-K225.
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

echo "==> emit zisk_block_body_summary ELF"
lake exe codegen --program zisk_block_body_summary --halt linux93 \
  -o gen-out/zisk_block_body_summary

REPO_ROOT="$(pwd)"

run_case() {
  local name="$1" txs="$2" ommers="$3" wdraws="$4"

  local in_file="$REPO_ROOT/gen-out/zisk_block_body_summary_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_block_body_summary_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys, rlp
tx = bytes.fromhex('f8500184ee6b280082520894aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa881bc16d674ec80000801ba01111111111111111111111111111111111111111111111111111111111111111a02222222222222222222222222222222222222222222222222222222222222222')
txs = [tx for _ in range($txs)]
ommers = [b'\\xee'*10 for _ in range($ommers)]
wdraws = [[i.to_bytes(2,'big'), i.to_bytes(4,'big'), b'\\xee'*20, b'\\xab\\xcd'] for i in range($wdraws)]
body_rlp = rlp.encode([txs, ommers, wdraws])
with open(sys.argv[1], 'wb') as f:
    record = struct.pack('<Q', len(body_rlp)) + body_rlp
    f.write(record)
    pad = (-len(record)) % 8
    if pad: f.write(b'\x00' * pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_block_body_summary.elf \
    -i "$in_file" -o "$out_file" -n 1000000 \
    >"$REPO_ROOT/gen-out/zisk_block_body_summary_${name}.emu.log" 2>&1 || true

  local status_le; status_le="$(xxd -p -l 8 "$out_file" | tr -d '\n')"
  local tx_le; tx_le="$(    dd if="$out_file" bs=1 skip=8  count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local om_le; om_le="$(    dd if="$out_file" bs=1 skip=16 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local wd_le; wd_le="$(    dd if="$out_file" bs=1 skip=24 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local actual_tx; actual_tx="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$tx_le'))[0])")"
  local actual_om; actual_om="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$om_le'))[0])")"
  local actual_wd; actual_wd="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$wd_le'))[0])")"

  if [[ "$actual_tx" == "$txs" && "$actual_om" == "$ommers" && "$actual_wd" == "$wdraws" ]]; then
    printf "  %-26s OK   tx=%s ommers=%s wdraws=%s\n" "$name" "$actual_tx" "$actual_om" "$actual_wd"
    return 0
  else
    printf "  %-26s FAIL tx=%s/%s om=%s/%s wd=%s/%s\n" "$name" "$actual_tx" "$txs" "$actual_om" "$ommers" "$actual_wd" "$wdraws"
    return 1
  fi
}

FAILED=0
run_case "all_zero"        0 0 0 || FAILED=1
run_case "two_tx_zero_w"   2 0 0 || FAILED=1
run_case "one_one_one"     1 1 1 || FAILED=1
run_case "complex"         3 2 5 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: block_body_summary returns (tx, ommers, withdrawal) counts"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
