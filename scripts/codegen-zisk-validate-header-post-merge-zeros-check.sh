#!/usr/bin/env bash
# codegen-zisk-validate-header-post-merge-zeros-check.sh -- PR-K220.
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

echo "==> emit zisk_validate_header_post_merge_zeros ELF"
lake exe codegen --program zisk_validate_header_post_merge_zeros --halt linux93 \
  -o gen-out/zisk_validate_header_post_merge_zeros

REPO_ROOT="$(pwd)"

# run_case <name> <ommers_ok> <diff> <nonce_hex> <exp_valid>
run_case() {
  local name="$1" oh_ok="$2" diff="$3" nonce_hex="$4" exp_valid="$5"

  local in_file="$REPO_ROOT/gen-out/zisk_validate_header_post_merge_zeros_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_validate_header_post_merge_zeros_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys, rlp
def u_be(n):
    if n == 0: return b''
    return n.to_bytes((n.bit_length() + 7) // 8, 'big')
EMPTY_OMMERS_HASH = bytes.fromhex('1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347')
oh_ok = $oh_ok == 1
d = $diff
n = bytes.fromhex('$nonce_hex')
ommers = EMPTY_OMMERS_HASH if oh_ok else b'\\xff'*32
fields = [
    b'\\xa1'*32, ommers, b'\\xa3'*20, b'\\xa4'*32, b'\\xa5'*32,
    b'\\xa6'*32, b'\\x00'*256, u_be(d), b'\\x01', b'\\x83\\xff\\xff\\xff',
    b'', b'\\x83\\x01\\x02\\x03', b'', b'\\xa7'*32, n,
]
header_rlp = rlp.encode(fields)
with open(sys.argv[1], 'wb') as f:
    record = struct.pack('<Q', len(header_rlp)) + header_rlp
    f.write(record)
    pad = (-len(record)) % 8
    if pad: f.write(b'\x00' * pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_validate_header_post_merge_zeros.elf \
    -i "$in_file" -o "$out_file" -n 1000000 \
    >"$REPO_ROOT/gen-out/zisk_validate_header_post_merge_zeros_${name}.emu.log" 2>&1 || true

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
run_case "all_post_merge_zero" 1 0 "0000000000000000" 1 || FAILED=1
run_case "bad_ommers"          0 0 "0000000000000000" 0 || FAILED=1
run_case "nonzero_difficulty"  1 1 "0000000000000000" 0 || FAILED=1
run_case "nonzero_nonce"       1 0 "0000000000000001" 0 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: validate_header_post_merge_zeros enforces all 3 EIP-3675 zero invariants"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
