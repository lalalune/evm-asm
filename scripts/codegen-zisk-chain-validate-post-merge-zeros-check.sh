#!/usr/bin/env bash
# codegen-zisk-chain-validate-post-merge-zeros-check.sh -- PR-K221.
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

echo "==> emit zisk_chain_validate_post_merge_zeros ELF"
lake exe codegen --program zisk_chain_validate_post_merge_zeros --halt linux93 \
  -o gen-out/zisk_chain_validate_post_merge_zeros

REPO_ROOT="$(pwd)"

# spec: list of (broken_field: 'none' | 'ommers' | 'diff' | 'nonce')
run_case() {
  local name="$1" spec="$2" exp_valid="$3" exp_bad="$4"

  local in_file="$REPO_ROOT/gen-out/zisk_chain_validate_post_merge_zeros_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_chain_validate_post_merge_zeros_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys, rlp
def u_be(n):
    if n == 0: return b''
    return n.to_bytes((n.bit_length() + 7) // 8, 'big')
EMPTY_OMMERS_HASH = bytes.fromhex('1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')

def make_header(broken):
    ommers = EMPTY_OMMERS_HASH if broken != 'ommers' else b'\\xff'*32
    diff   = 0 if broken != 'diff' else 1
    nonce  = b'\\x00'*8 if broken != 'nonce' else b'\\x00'*7 + b'\\x01'
    return rlp.encode([
        b'\\xa1'*32, ommers, b'\\xa3'*20, b'\\xa4'*32, b'\\xa5'*32,
        b'\\xa6'*32, b'\\x00'*256, u_be(diff), b'\\x01', b'\\x83\\xff\\xff\\xff',
        b'', b'\\x83\\x01\\x02\\x03', b'', b'\\xa7'*32, nonce,
    ])

spec = $spec
headers = [make_header(b) for b in spec]
N = len(headers)
lengths = b''.join(struct.pack('<Q', len(h)) for h in headers)
flat = b''.join(headers)

with open(sys.argv[1], 'wb') as f:
    record = struct.pack('<Q', N) + lengths + flat
    f.write(record)
    pad = (-len(record)) % 8
    if pad: f.write(b'\x00' * pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_chain_validate_post_merge_zeros.elf \
    -i "$in_file" -o "$out_file" -n 5000000 \
    >"$REPO_ROOT/gen-out/zisk_chain_validate_post_merge_zeros_${name}.emu.log" 2>&1 || true

  local valid_le; valid_le="$(dd if="$out_file" bs=1 skip=8  count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local bad_le;   bad_le="$(  dd if="$out_file" bs=1 skip=16 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local valid bad
  valid="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$valid_le'))[0])")"
  bad="$(  python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$bad_le'))[0])")"

  if [[ "$valid" == "$exp_valid" && "$bad" == "$exp_bad" ]]; then
    printf "  %-28s OK   valid=%s bad=%s\n" "$name" "$valid" "$bad"
    return 0
  else
    printf "  %-28s FAIL valid=%s/%s bad=%s/%s\n" "$name" "$valid" "$exp_valid" "$bad" "$exp_bad"
    return 1
  fi
}

FAILED=0
run_case "empty" "[]" 1 0 || FAILED=1
run_case "all_clean" "['none','none','none']" 1 0 || FAILED=1
run_case "bad_at_index_1_ommers" "['none','ommers','none']" 0 1 || FAILED=1
run_case "bad_at_index_2_diff"   "['none','none','diff']"   0 2 || FAILED=1
run_case "bad_at_index_0_nonce"  "['nonce','none','none']"  0 0 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: chain_validate_post_merge_zeros iterates K220 and reports first bad"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
