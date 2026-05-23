#!/usr/bin/env bash
# codegen-zisk-block-count-withdrawals-check.sh -- PR-K124.
#
# Count withdrawals in a block body.
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

echo "==> emit zisk_block_count_withdrawals ELF"
lake exe codegen --program zisk_block_count_withdrawals --halt linux93 \
  -o gen-out/zisk_block_count_withdrawals

REPO_ROOT="$(pwd)"

# run_case <name> <wds_json>
run_case() {
  local name="$1" wds_json="$2"

  local in_file="$REPO_ROOT/gen-out/zisk_block_count_withdrawals_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_block_count_withdrawals_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import json, struct, sys, rlp
wds_raw = json.loads('''$wds_json''')
wds = []
for w in wds_raw:
    idx, vi, addr_hex, amt = w
    wds.append([idx, vi, bytes.fromhex(addr_hex), amt])
body_rlp = rlp.encode([[], [], wds])
with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(body_rlp)))
    f.write(body_rlp)
    pad = (-(8 + len(body_rlp))) % 8
    if pad: f.write(b'\x00' * pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_block_count_withdrawals.elf \
    -i "$in_file" -o "$out_file" -n 1000000 \
    >"$REPO_ROOT/gen-out/zisk_block_count_withdrawals_${name}.emu.log" 2>&1 || true

  local actual_status; actual_status="$(xxd -p -l 8 "$out_file" | tr -d '\n')"
  local actual_count_le; actual_count_le="$(dd if="$out_file" bs=1 skip=8 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local actual_count; actual_count="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$actual_count_le'))[0])")"
  local expected_count; expected_count="$(python3 -c "import json; print(len(json.loads('''$wds_json''')))")"

  if [[ "$actual_status" == "0000000000000000" && "$actual_count" == "$expected_count" ]]; then
    printf "  %-32s OK   count=%d\n" "$name" "$expected_count"
    return 0
  else
    printf "  %-32s FAIL status=0x%s count=%d expected=%d\n" "$name" "$actual_status" "$actual_count" "$expected_count"
    return 1
  fi
}

ALICE="aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
GWEI=$(python3 -c "print(10**9)")

FAILED=0
run_case "empty"                "[]"                                            || FAILED=1
run_case "one_wd"               "[[0, 1, \"$ALICE\", $GWEI]]"                   || FAILED=1
run_case "two_wd" \
  "[[0, 1, \"$ALICE\", $GWEI], [1, 2, \"$ALICE\", $GWEI]]"                      || FAILED=1
run_case "sixteen_wd"           "$(python3 -c "
import json
addr = '$ALICE'
print(json.dumps([[i, i+1000, addr, (i+1) * 10**9] for i in range(16)]))
")"                                                                              || FAILED=1
run_case "one_hundred_wd"       "$(python3 -c "
import json
addr = '$ALICE'
print(json.dumps([[i, i+1000, addr, (i+1) * 10**9] for i in range(100)]))
")"                                                                              || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: block_count_withdrawals returns len(block.withdrawals)"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
