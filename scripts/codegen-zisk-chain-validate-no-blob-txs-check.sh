#!/usr/bin/env bash
# codegen-zisk-chain-validate-no-blob-txs-check.sh -- PR-K258.
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

echo "==> emit zisk_chain_validate_no_blob_txs ELF"
lake exe codegen --program zisk_chain_validate_no_blob_txs --halt linux93 \
  -o gen-out/zisk_chain_validate_no_blob_txs

REPO_ROOT="$(pwd)"

run_case() {
  local name="$1" blob_gas_list="$2" cancun_list="$3" exp_valid="$4" exp_bad="$5"

  local in_file="$REPO_ROOT/gen-out/zisk_chain_validate_no_blob_txs_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_chain_validate_no_blob_txs_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys, rlp
def u_be(n):
    if n == 0: return b''
    return n.to_bytes((n.bit_length() + 7) // 8, 'big')

def make_header_pre(idx):
    return rlp.encode([
        b'\\xa1'*32, b'\\xa2'*32, b'\\xa3'*20, b'\\xa4'*32, b'\\xa5'*32,
        b'\\xa6'*32, b'\\x00'*256, b'', b'\\x01', b'\\x83\\xff\\xff\\xff',
        b'', b'\\x83\\x01\\x02\\x03', b'', b'\\xa7'*32, b'\\x00'*8,
    ])

def make_header_cancun(blob_gas_used):
    return rlp.encode([
        b'\\xa1'*32, b'\\xa2'*32, b'\\xa3'*20, b'\\xa4'*32, b'\\xa5'*32,
        b'\\xa6'*32, b'\\x00'*256, b'', b'\\x01', b'\\x83\\xff\\xff\\xff',
        b'', b'\\x83\\x01\\x02\\x03', b'', b'\\xa7'*32, b'\\x00'*8,
        b'\\x82\\x01\\x00', b'\\xa8'*32,
        u_be(blob_gas_used),
        u_be(0),
    ])

gases = $blob_gas_list
cancun = $cancun_list
headers = []
for g, c in zip(gases, cancun):
    if c:
        headers.append(make_header_cancun(g))
    else:
        headers.append(make_header_pre(g))
N = len(headers)
lengths = b''.join(struct.pack('<Q', len(h)) for h in headers)
flat = b''.join(headers)
with open(sys.argv[1], 'wb') as f:
    record = struct.pack('<Q', N) + lengths + flat
    f.write(record)
    pad = (-len(record)) % 8
    if pad: f.write(b'\x00' * pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_chain_validate_no_blob_txs.elf \
    -i "$in_file" -o "$out_file" -n 5000000 \
    >"$REPO_ROOT/gen-out/zisk_chain_validate_no_blob_txs_${name}.emu.log" 2>&1 || true

  local v_le; v_le="$(dd if="$out_file" bs=1 skip=8 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local b_le; b_le="$(dd if="$out_file" bs=1 skip=16 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local valid bad
  valid="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$v_le'))[0])")"
  bad="$(  python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$b_le'))[0])")"

  if [[ "$valid" == "$exp_valid" && "$bad" == "$exp_bad" ]]; then
    printf "  %-26s OK   valid=%s bad=%s\n" "$name" "$valid" "$bad"
    return 0
  else
    printf "  %-26s FAIL valid=%s/%s bad=%s/%s\n" "$name" "$valid" "$exp_valid" "$bad" "$exp_bad"
    return 1
  fi
}

FAILED=0
run_case "vacuous_empty"      "[]"        "[]"          1 0 || FAILED=1
run_case "single_pre"         "[0]"       "[False]"     1 0 || FAILED=1
run_case "single_cancun_zero" "[0]"       "[True]"      1 0 || FAILED=1
run_case "single_cancun_some" "[131072]"  "[True]"      0 0 || FAILED=1
run_case "mixed_all_zero"     "[0,0,0]"   "[False,True,True]" 1 0 || FAILED=1
run_case "blob_at_index_1"    "[0,131072,0]" "[True,True,True]" 0 1 || FAILED=1
run_case "blob_at_index_2"    "[0,0,262144]" "[True,True,True]" 0 2 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: chain_validate_no_blob_txs enforces blob_gas_used == 0 per header"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
