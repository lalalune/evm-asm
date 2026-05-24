#!/usr/bin/env bash
# codegen-zisk-validate-parent-hash-link-check.sh -- PR-K173.
#
# Validate that child.parent_hash == keccak256(parent_rlp). Per-step
# check inside `validate_headers`.
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

echo "==> emit zisk_validate_parent_hash_link ELF"
lake exe codegen --program zisk_validate_parent_hash_link --halt linux93 \
  -o gen-out/zisk_validate_parent_hash_link

REPO_ROOT="$(pwd)"

# run_case <name> <parent_phash_override_or_empty> <make_child_garbage 0/1>
#                <make_child_short_field0 0/1> <exp_status> <exp_valid>
#
# parent_phash_override_or_empty:
#   ""              -- child.parent_hash = keccak(parent_rlp) (matching)
#   "<32B hex>"     -- splice an explicit value into child.field[0]
run_case() {
  local name="$1" pho="$2" garbage="$3" shortf0="$4" exp_status="$5" exp_valid="$6"

  local in_file="$REPO_ROOT/gen-out/zisk_validate_parent_hash_link_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_validate_parent_hash_link_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys, rlp
try:
    from Crypto.Hash import keccak
    def keccak256(b):
        h = keccak.new(digest_bits=256); h.update(b); return h.digest()
except Exception:
    import sha3
    def keccak256(b): return sha3.keccak_256(b).digest()

pho = '$pho'
garbage_child = $garbage == 1
short_f0 = $shortf0 == 1

# Build a representative parent header (London-ish, 16 fields).
parent_fields = [
    b'\\xa1'*32, b'\\xa2'*32, b'\\xa3'*20, b'\\xa4'*32, b'\\xa5'*32,
    b'\\xa6'*32, b'\\x00'*256, b'', b'\\x83\\xa0\\x00\\x00', b'\\x83\\xff\\xff\\xff',
    b'\\x82\\x02\\x00', b'\\x83\\x01\\x02\\x03', b'', b'\\xa7'*32, b'\\x00'*8,
    b'\\x82\\x12\\x34',
]
parent_rlp = rlp.encode(parent_fields)
expected_block_hash = keccak256(parent_rlp)

if pho == '':
    claimed = expected_block_hash
else:
    claimed = bytes.fromhex(pho)

if short_f0:
    field0 = b'\\xc1' * 16    # 16-byte 'parent_hash' -> wrong size
else:
    field0 = claimed

child_fields = [
    field0,                # field 0 = parent_hash
    b'\\xb2'*32,             # ommers_hash
    b'\\xb3'*20,             # beneficiary
    b'\\xb4'*32,             # state_root
    b'\\xb5'*32,             # transactions_root
    b'\\xb6'*32,             # receipts_root
    b'\\x00'*256,            # logs_bloom
    b'',                    # difficulty
    b'\\x83\\xa0\\x00\\x01',  # number = parent.number + 1
    b'\\x83\\xff\\xff\\xff',  # gas_limit
    b'\\x82\\x02\\x00',       # gas_used
    b'\\x83\\x01\\x02\\x04',  # timestamp
    b'',                    # extra_data
    b'\\xb7'*32,             # prev_randao
    b'\\x00'*8,              # nonce
    b'\\x82\\x12\\x34',       # base_fee
]

if garbage_child:
    child_rlp = b'\\x00'       # not a valid RLP list -- parse_fail
else:
    child_rlp = rlp.encode(child_fields)

with open(sys.argv[1], 'wb') as f:
    record = struct.pack('<Q', len(parent_rlp)) + \
             struct.pack('<Q', len(child_rlp)) + \
             parent_rlp + child_rlp
    f.write(record)
    pad = (-len(record)) % 8
    if pad: f.write(b'\x00' * pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_validate_parent_hash_link.elf \
    -i "$in_file" -o "$out_file" -n 5000000 \
    >"$REPO_ROOT/gen-out/zisk_validate_parent_hash_link_${name}.emu.log" 2>&1 || true

  local status_le; status_le="$(xxd -p -l 8 "$out_file" | tr -d '\n')"
  local valid_le;  valid_le="$( dd if="$out_file" bs=1 skip=8 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local status valid
  status="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$status_le'))[0])")"
  valid="$( python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$valid_le'))[0])")"

  if [[ "$status" == "$exp_status" && "$valid" == "$exp_valid" ]]; then
    printf "  %-30s OK   status=%s valid=%s\n" "$name" "$status" "$valid"
    return 0
  else
    printf "  %-30s FAIL status=%s (exp %s) valid=%s (exp %s)\n" \
      "$name" "$status" "$exp_status" "$valid" "$exp_valid"
    return 1
  fi
}

WRONG="ffeeddccbbaa99887766554433221100ffeeddccbbaa99887766554433221100"

FAILED=0
# Correct parent_hash -> valid=1
run_case "match"               ""        0 0 0 1 || FAILED=1
# Wrong parent_hash spliced in -> valid=0
run_case "mismatch_wrong_hash" "$WRONG"  0 0 0 0 || FAILED=1
# Short parent_hash (16 bytes) -> size_fail
run_case "size_fail_short_f0"  ""        0 1 2 0 || FAILED=1
# Garbage child RLP -> parse_fail
run_case "parse_fail_garbage"  ""        1 0 1 0 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: validate_parent_hash_link accepts matching parent_hash, rejects mismatches"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
