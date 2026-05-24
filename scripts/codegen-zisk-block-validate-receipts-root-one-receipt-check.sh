#!/usr/bin/env bash
# codegen-zisk-block-validate-receipts-root-one-receipt-check.sh -- PR-K193.
#
# N=1 variant for receipts_root.
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

echo "==> emit zisk_block_validate_receipts_root_one_receipt ELF"
lake exe codegen --program zisk_block_validate_receipts_root_one_receipt --halt linux93 \
  -o gen-out/zisk_block_validate_receipts_root_one_receipt

REPO_ROOT="$(pwd)"

# run_case <name> <receipt_py_expr> <override_or_special> <exp_status> <exp_valid>
run_case() {
  local name="$1" r_expr="$2" override="$3" exp_status="$4" exp_valid="$5"

  local in_file="$REPO_ROOT/gen-out/zisk_block_validate_receipts_root_one_receipt_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_block_validate_receipts_root_one_receipt_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys, rlp
try:
    from Crypto.Hash import keccak
    def keccak256(b):
        h = keccak.new(digest_bits=256); h.update(b); return h.digest()
except Exception:
    import sha3
    def keccak256(b): return sha3.keccak_256(b).digest()

receipt_rlp = $r_expr
override = '$override'

def hp_leaf(nibbles, value):
    flag = 2 + (len(nibbles) & 1)
    hp = bytearray()
    if len(nibbles) % 2 == 1:
        hp.append((flag << 4) | nibbles[0]); i = 1
    else:
        hp.append(flag << 4); i = 0
    while i < len(nibbles):
        hp.append((nibbles[i] << 4) | nibbles[i+1]); i += 2
    return rlp.encode([bytes(hp), value])

correct_root = keccak256(hp_leaf([8, 0], receipt_rlp))

if override == 'garbage':
    header_rlp = b'\\x00'
else:
    if override == '':
        field5 = correct_root
    elif override == 'short':
        field5 = b'\\xaa'*16
    else:
        field5 = bytes.fromhex(override)
    fields = [
        b'\\x11'*32, b'\\x22'*32, b'\\x33'*20, b'\\x44'*32, b'\\x55'*32,
        field5, b'\\x00'*256, b'', b'\\x01', b'\\x83\\xff\\xff\\xff',
        b'', b'\\x83\\x01\\x02\\x03', b'', b'\\x77'*32, b'\\x00'*8,
    ]
    header_rlp = rlp.encode(fields)

with open(sys.argv[1], 'wb') as f:
    record = struct.pack('<Q', len(header_rlp)) + \
             struct.pack('<Q', len(receipt_rlp)) + \
             header_rlp + receipt_rlp
    f.write(record)
    pad = (-len(record)) % 8
    if pad: f.write(b'\x00' * pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_block_validate_receipts_root_one_receipt.elf \
    -i "$in_file" -o "$out_file" -n 5000000 \
    >"$REPO_ROOT/gen-out/zisk_block_validate_receipts_root_one_receipt_${name}.emu.log" 2>&1 || true

  local status_le; status_le="$(xxd -p -l 8 "$out_file" | tr -d '\n')"
  local valid_le;  valid_le="$( dd if="$out_file" bs=1 skip=8 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local status valid
  status="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$status_le'))[0])")"
  valid="$( python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$valid_le'))[0])")"

  if [[ "$status" == "$exp_status" && "$valid" == "$exp_valid" ]]; then
    printf "  %-28s OK   status=%s valid=%s\n" "$name" "$status" "$valid"
    return 0
  else
    printf "  %-28s FAIL status=%s/%s valid=%s/%s\n" \
      "$name" "$status" "$exp_status" "$valid" "$exp_valid"
    return 1
  fi
}

# Legacy receipt: rlp([status, cum_gas_used, bloom, logs])
RECEIPT="rlp.encode([b'\\x01', b'\\x83\\x52\\x08', b'\\x00'*256, []])"
WRONG="ffeeddccbbaa99887766554433221100ffeeddccbbaa99887766554433221100"

FAILED=0
run_case "match_one_receipt"     "$RECEIPT" ""        0 1 || FAILED=1
run_case "mismatch_wrong_root"   "$RECEIPT" "$WRONG"  0 0 || FAILED=1
run_case "size_fail_short_f5"    "$RECEIPT" "short"   2 0 || FAILED=1
run_case "parse_fail_garbage"    "$RECEIPT" "garbage" 1 0 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: block_validate_receipts_root_one_receipt accepts matching root, rejects others"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
