#!/usr/bin/env bash
# codegen-zisk-chain-validate-post-merge-full-check.sh -- PR-K290.
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

echo "==> emit zisk_chain_validate_post_merge_full ELF"
lake exe codegen --program zisk_chain_validate_post_merge_full --halt linux93 \
  -o gen-out/zisk_chain_validate_post_merge_full

REPO_ROOT="$(pwd)"

# kind codes: 1=diff, 2=nonce, 3=ommers
# Encoded bad_index = (i << 2) | kind
EMPTY="1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347"
NONEMPTY="aabbccddeeff0011aabbccddeeff0011aabbccddeeff0011aabbccddeeff0011"

run_case() {
  local name="$1" specs_list="$2" exp_status="$3" exp_valid="$4" exp_encoded="$5"

  local in_file="$REPO_ROOT/gen-out/zisk_chain_validate_post_merge_full_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_chain_validate_post_merge_full_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys, rlp
def u_be(n):
    if n == 0: return b''
    return n.to_bytes((n.bit_length() + 7) // 8, 'big')

def make_header(omh_hex, diff, nonce_int):
    omh = bytes.fromhex(omh_hex)
    nonce = nonce_int.to_bytes(8, 'big') if nonce_int else b'\\x00'*8
    return rlp.encode([
        b'\\xa1'*32, omh, b'\\xa3'*20, b'\\xa4'*32, b'\\xa5'*32,
        b'\\xa6'*32, b'\\x00'*256, u_be(diff), b'\\x01', b'\\x83\\xff\\xff\\xff',
        b'', b'\\x83\\x01\\x02\\x03', b'', b'\\xa7'*32, nonce,
    ])

vals = $specs_list  # list of (omh_hex, diff, nonce) tuples
headers = [make_header(*v) for v in vals]
N = len(headers)
lengths = b''.join(struct.pack('<Q', len(h)) for h in headers)
flat = b''.join(headers)
with open(sys.argv[1], 'wb') as f:
    record = struct.pack('<Q', N) + lengths + flat
    f.write(record)
    pad = (-len(record)) % 8
    if pad: f.write(b'\\x00' * pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_chain_validate_post_merge_full.elf \
    -i "$in_file" -o "$out_file" -n 5000000 \
    >"$REPO_ROOT/gen-out/zisk_chain_validate_post_merge_full_${name}.emu.log" 2>&1 || true

  local s_le; s_le="$(dd if="$out_file" bs=1 skip=0  count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local v_le; v_le="$(dd if="$out_file" bs=1 skip=8  count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local e_le; e_le="$(dd if="$out_file" bs=1 skip=16 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local status valid enc
  status="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$s_le'))[0])")"
  valid="$( python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$v_le'))[0])")"
  enc="$(   python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$e_le'))[0])")"

  if [[ "$status" == "$exp_status" && "$valid" == "$exp_valid" && "$enc" == "$exp_encoded" ]]; then
    printf "  %-32s OK   status=%s valid=%s enc=%s\n" "$name" "$status" "$valid" "$enc"
    return 0
  else
    printf "  %-32s FAIL status=%s/%s valid=%s/%s enc=%s/%s\n" "$name" "$status" "$exp_status" "$valid" "$exp_valid" "$enc" "$exp_encoded"
    return 1
  fi
}

FAILED=0
# All post-merge: omh=EMPTY, diff=0, nonce=0
run_case "empty"                   "[]"  0 1 0 || FAILED=1
run_case "single_post_merge"       "[('$EMPTY', 0, 0)]"  0 1 0 || FAILED=1
run_case "single_diff_fail"        "[('$EMPTY', 1, 0)]"  0 0 1 || FAILED=1  # (0<<2)|1=1
run_case "single_nonce_fail"       "[('$EMPTY', 0, 7)]"  0 0 2 || FAILED=1  # (0<<2)|2=2
run_case "single_omh_fail"         "[('$NONEMPTY', 0, 0)]" 0 0 3 || FAILED=1  # (0<<2)|3=3
run_case "three_diff_fail_at_2"    "[('$EMPTY', 0, 0), ('$EMPTY', 0, 0), ('$EMPTY', 5, 0)]" 0 0 9 || FAILED=1  # (2<<2)|1=9
run_case "three_nonce_fail_at_1"   "[('$EMPTY', 0, 0), ('$EMPTY', 0, 99), ('$EMPTY', 0, 0)]" 0 0 6 || FAILED=1  # (1<<2)|2=6
run_case "three_omh_fail_at_1"     "[('$EMPTY', 0, 0), ('$NONEMPTY', 0, 0), ('$EMPTY', 0, 0)]" 0 0 7 || FAILED=1  # (1<<2)|3=7
run_case "five_all_pass"           "[('$EMPTY', 0, 0)] * 5" 0 1 0 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: chain_validate_post_merge_full checks all three EIP-3675 invariants"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
