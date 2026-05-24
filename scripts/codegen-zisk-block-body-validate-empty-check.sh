#!/usr/bin/env bash
# codegen-zisk-block-body-validate-empty-check.sh -- PR-K226.
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

echo "==> emit zisk_block_body_validate_empty ELF"
lake exe codegen --program zisk_block_body_validate_empty --halt linux93 \
  -o gen-out/zisk_block_body_validate_empty

REPO_ROOT="$(pwd)"

run_case() {
  local name="$1" txs="$2" ommers="$3" wdraws="$4" exp_valid="$5"

  local in_file="$REPO_ROOT/gen-out/zisk_block_body_validate_empty_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_block_body_validate_empty_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys, rlp
tx_count = $txs
om_count = $ommers
wd_count = $wdraws
txs = [b'\\xaa'*10 for _ in range(tx_count)]
ommers = [b'\\xee'*10 for _ in range(om_count)]
wdraws = [[i.to_bytes(2,'big'), i.to_bytes(4,'big'), b'\\xee'*20, b'\\xab\\xcd'] for i in range(wd_count)]
body_rlp = rlp.encode([txs, ommers, wdraws])
with open(sys.argv[1], 'wb') as f:
    record = struct.pack('<Q', len(body_rlp)) + body_rlp
    f.write(record)
    pad = (-len(record)) % 8
    if pad: f.write(b'\x00' * pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_block_body_validate_empty.elf \
    -i "$in_file" -o "$out_file" -n 1000000 \
    >"$REPO_ROOT/gen-out/zisk_block_body_validate_empty_${name}.emu.log" 2>&1 || true

  local valid_le; valid_le="$(dd if="$out_file" bs=1 skip=8 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local valid; valid="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$valid_le'))[0])")"

  if [[ "$valid" == "$exp_valid" ]]; then
    printf "  %-26s OK   valid=%s\n" "$name" "$valid"
    return 0
  else
    printf "  %-26s FAIL valid=%s/%s\n" "$name" "$valid" "$exp_valid"
    return 1
  fi
}

FAILED=0
run_case "all_empty"      0 0 0 1 || FAILED=1
run_case "has_tx"         1 0 0 0 || FAILED=1
run_case "has_ommers"     0 1 0 0 || FAILED=1
run_case "has_withdrawal" 0 0 1 0 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: block_body_validate_empty enforces all-3-lists-empty predicate"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
