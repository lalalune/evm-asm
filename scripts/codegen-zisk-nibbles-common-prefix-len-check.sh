#!/usr/bin/env bash
# codegen-zisk-nibbles-common-prefix-len-check.sh -- PR-K166.
#
# Common prefix length of two nibble arrays.
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

echo "==> emit zisk_nibbles_common_prefix_len ELF"
lake exe codegen --program zisk_nibbles_common_prefix_len --halt linux93 \
  -o gen-out/zisk_nibbles_common_prefix_len

REPO_ROOT="$(pwd)"

# run_case <name> <nibbles_a_hex> <nibbles_b_hex> <expected_cpl>
# nibbles_*_hex: each byte = one nibble (low 4 bits)
run_case() {
  local name="$1" a="$2" b="$3" exp="$4"

  local in_file="$REPO_ROOT/gen-out/zisk_nibbles_common_prefix_len_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_nibbles_common_prefix_len_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys
a = bytes.fromhex('$a')
b = bytes.fromhex('$b')
with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(a)))
    f.write(struct.pack('<Q', len(b)))
    f.write(a + b)
    pad = (-(16 + len(a) + len(b))) % 8
    if pad: f.write(b'\x00' * pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_nibbles_common_prefix_len.elf \
    -i "$in_file" -o "$out_file" -n 100000 \
    >"$REPO_ROOT/gen-out/zisk_nibbles_common_prefix_len_${name}.emu.log" 2>&1 || true

  local actual_status; actual_status="$(xxd -p -l 8 "$out_file" | tr -d '\n')"
  local actual_cpl_le; actual_cpl_le="$(dd if="$out_file" bs=1 skip=8 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local actual_cpl; actual_cpl="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$actual_cpl_le'))[0])")"

  if [[ "$actual_status" == "0000000000000000" && "$actual_cpl" == "$exp" ]]; then
    printf "  %-30s OK   cpl=%d\n" "$name" "$exp"
    return 0
  else
    printf "  %-30s FAIL status=0x%s cpl=%d expected=%d\n" "$name" "$actual_status" "$actual_cpl" "$exp"
    return 1
  fi
}

FAILED=0
# Identical short
run_case "identical_2nib"       "0a0b"             "0a0b"             2 || FAILED=1
# Identical longer
run_case "identical_8nib"       "0102030405060708" "0102030405060708" 8 || FAILED=1
# All different (cpl = 0)
run_case "all_different"        "0a0b"             "0c0d"             0 || FAILED=1
# rlp(0)=0x80 vs rlp(1)=0x01 nibble shape -> cpl=0
run_case "rlp0_vs_rlp1"         "0800"             "0001"             0 || FAILED=1
# rlp(2)=0x02 vs rlp(3)=0x03 nibble shape -> cpl=1 (both start with 0x0)
run_case "rlp2_vs_rlp3"         "0002"             "0003"             1 || FAILED=1
# Same nibbles up to mid then diverge
run_case "diverge_mid"          "0a0b0c0d0e"       "0a0b0c0f0e"       3 || FAILED=1
# One is empty
run_case "empty_a"              ""                 "0a0b"             0 || FAILED=1
run_case "empty_b"              "0a0b"             ""                 0 || FAILED=1
run_case "both_empty"           ""                 ""                 0 || FAILED=1
# One is a prefix of the other
run_case "a_prefix_of_b"        "0a0b"             "0a0b0c0d"         2 || FAILED=1
run_case "b_prefix_of_a"        "0a0b0c0d"         "0a0b"             2 || FAILED=1
# Long shared prefix (state-trie depth)
run_case "long_shared_prefix"   "$(python3 -c "print('0a' * 32)")" "$(python3 -c "print('0a' * 31 + '0b')")" 31 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: nibbles_common_prefix_len matches expected lengths"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
