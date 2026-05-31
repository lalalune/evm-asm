#!/usr/bin/env bash
# codegen-zisk-withdrawals-root-at-block-number-check.sh
#
# Number-keyed header.withdrawals_root extractor.
#
# Output (40 bytes):
#   bytes  0.. 8 : status (0..3)
#   bytes  8..40 : withdrawals_root (32 B; 0 on failure)
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

echo "==> emit zisk_withdrawals_root_at_block_number ELF"
lake exe codegen --program zisk_withdrawals_root_at_block_number \
  --halt linux93 \
  -o gen-out/zisk_withdrawals_root_at_block_number

REPO_ROOT="$(pwd)"

run_case() {
  local name="$1"; shift
  local mode="$1"; shift
  local target="$1"; shift

  local in_file="$REPO_ROOT/gen-out/zisk_wrbn_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_wrbn_${name}.output"
  local exp_file="$REPO_ROOT/gen-out/zisk_wrbn_${name}.expected"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys
import rlp

def build_ssz_section(elements):
    n = len(elements)
    if n == 0: return b''
    section = b''
    offset = 4 * n
    for e in elements:
        section += struct.pack('<I', offset); offset += len(e)
    for e in elements: section += e
    return section

def shortest_be(n):
    if n == 0: return b''
    nbytes = (n.bit_length() + 7) // 8
    return n.to_bytes(nbytes, 'big')

def encode_header(number_val, withdrawals_root):
    # Amsterdam header field layout. withdrawals_root is field 16.
    fields = [
        b'\\x11'*32,                # 0  parent_hash
        b'\\x22'*32,                # 1  ommers_hash
        b'\\x33'*20,                # 2  beneficiary
        b'\\x44'*32,                # 3  state_root
        b'\\x55'*32,                # 4  transactions_root
        b'\\x66'*32,                # 5  receipts_root
        b'\\x00'*256,               # 6  logs_bloom
        b'',                        # 7  difficulty
        shortest_be(number_val),    # 8  number
        b'\\x83\\xff\\xff\\xff',    # 9  gas_limit
        b'',                        # 10 gas_used
        b'\\x83\\x01\\x02\\x03',    # 11 timestamp
        b'',                        # 12 extra_data
        b'\\x77'*32,                # 13 prev_randao
        b'\\x00'*8,                 # 14 nonce
        b'',                        # 15 base_fee_per_gas
        withdrawals_root,           # 16 withdrawals_root
        b'',                        # 17 blob_gas_used
        b'',                        # 18 excess_blob_gas
        b'\\x99'*32,                # 19 parent_beacon_block_root
    ]
    return rlp.encode(fields)

EMPTY_TRIE = bytes.fromhex('56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421')

mode = '$mode'
target = int('$target')

if mode == 'real_withdrawals':
    wd_root = b'\\xcc' * 32
    h0 = encode_header(target, wd_root)
    witness_headers = build_ssz_section([h0])
    expected = struct.pack('<Q', 0) + wd_root
elif mode == 'empty_trie_root':
    wd_root = EMPTY_TRIE
    h0 = encode_header(target, wd_root)
    witness_headers = build_ssz_section([h0])
    expected = struct.pack('<Q', 0) + wd_root
elif mode == 'pick_second_of_two':
    decoy = b'\\xee' * 32
    real = bytes(range(32))
    h0 = encode_header(100, decoy)
    h1 = encode_header(target, real)
    witness_headers = build_ssz_section([h0, h1])
    expected = struct.pack('<Q', 0) + real
elif mode == 'number_miss':
    wd_root = b'\\xcc' * 32
    h0 = encode_header(100, wd_root)
    witness_headers = build_ssz_section([h0])
    expected = struct.pack('<Q', 1) + b'\\x00' * 32
else:
    raise SystemExit('bad mode')

with open(sys.argv[1], 'wb') as f:
    record = (
        struct.pack('<Q', len(witness_headers))
        + struct.pack('<Q', target)
        + witness_headers
    )
    f.write(record)
    pad = (-len(record)) % 8
    if pad: f.write(b'\\x00' * pad)

with open(sys.argv[2], 'wb') as f:
    f.write(expected)
" "$in_file" "$exp_file"

  "$ZISKEMU" -e gen-out/zisk_withdrawals_root_at_block_number.elf \
    -i "$in_file" -o "$out_file" -n 4000000 \
    >"$REPO_ROOT/gen-out/zisk_wrbn_${name}.emu.log" 2>&1 || true

  local exp_size; exp_size="$(stat -c%s "$exp_file")"
  local actual expected
  actual="$(xxd -p -l "$exp_size" "$out_file" 2>/dev/null | tr -d '\n')"
  expected="$(xxd -p -l "$exp_size" "$exp_file" 2>/dev/null | tr -d '\n')"

  if [[ "$actual" == "$expected" ]]; then
    printf "  %-36s OK   %d bytes match\n" "$name" "$exp_size"
    return 0
  else
    printf "  %-36s FAIL\n    expected: %s\n    actual:   %s\n" \
      "$name" "$expected" "$actual"
    return 1
  fi
}

FAILED=0
run_case "real_withdrawals_root"     real_withdrawals 101 || FAILED=1
run_case "empty_trie_root"           empty_trie_root 101 || FAILED=1
run_case "pick_second_of_two"        pick_second_of_two 101 || FAILED=1
run_case "number_not_in_section"     number_miss 999 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: withdrawals_root_at_block_number end-to-end"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
