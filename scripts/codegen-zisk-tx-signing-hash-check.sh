#!/usr/bin/env bash
# codegen-zisk-tx-signing-hash-check.sh -- PR-K145.
#
# Unified tx signing-hash builder: keccak256([type_prefix?] || rlp([first n fields])).
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

echo "==> emit zisk_tx_signing_hash ELF"
lake exe codegen --program zisk_tx_signing_hash --halt linux93 \
  -o gen-out/zisk_tx_signing_hash

REPO_ROOT="$(pwd)"

# run_case <name> <fields_json> <n> <type_prefix>
run_case() {
  local name="$1" fields="$2" n="$3" prefix="$4"

  local in_file="$REPO_ROOT/gen-out/zisk_tx_signing_hash_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_tx_signing_hash_${name}.output"
  local exp_hex_file="$REPO_ROOT/gen-out/zisk_tx_signing_hash_${name}.expected.hex"

  uv run --directory execution-specs --quiet python3 -c "
import hashlib, json, struct, sys, rlp
try:
    from Crypto.Hash import keccak
    def keccak256(b):
        h = keccak.new(digest_bits=256); h.update(b); return h.digest()
except Exception:
    # Fallback to pysha3 if installed
    import sha3
    def keccak256(b): return sha3.keccak_256(b).digest()

fields_raw = json.loads('''$fields''')
def conv(x):
    if isinstance(x, str) and x.startswith('hex:'): return bytes.fromhex(x[4:])
    if isinstance(x, list): return [conv(e) for e in x]
    return x
fields = [conv(f) for f in fields_raw]
n = $n
prefix = $prefix
inner_rlp = rlp.encode(fields)
truncated = rlp.encode(fields[:n])
hash_input = (bytes([prefix]) if prefix != 0 else b'') + truncated
expected = keccak256(hash_input)
with open(sys.argv[1], 'wb') as f:
    f.write(struct.pack('<Q', len(inner_rlp)))
    f.write(struct.pack('<Q', n))
    f.write(struct.pack('<Q', prefix))
    f.write(inner_rlp)
    pad = (-(24 + len(inner_rlp))) % 8
    if pad: f.write(b'\x00' * pad)
with open(sys.argv[2], 'w') as f:
    f.write(expected.hex())
" "$in_file" "$exp_hex_file"

  "$ZISKEMU" -e gen-out/zisk_tx_signing_hash.elf \
    -i "$in_file" -o "$out_file" -n 5000000 \
    >"$REPO_ROOT/gen-out/zisk_tx_signing_hash_${name}.emu.log" 2>&1 || true

  local actual_status; actual_status="$(xxd -p -l 8 "$out_file" | tr -d '\n')"
  local actual_hash;   actual_hash="$(dd if="$out_file" bs=1 skip=8 count=32 2>/dev/null | xxd -p | tr -d '\n')"
  local expected_hex;  expected_hex="$(cat "$exp_hex_file")"

  if [[ "$actual_status" == "0000000000000000" && "$actual_hash" == "$expected_hex" ]]; then
    printf "  %-30s OK   n=%d prefix=0x%02x hash=%s...\n" "$name" "$n" "$prefix" "${actual_hash:0:16}"
    return 0
  else
    printf "  %-30s FAIL status=0x%s\n" "$name" "$actual_status"
    printf "      actual:   %s\n" "$actual_hash"
    printf "      expected: %s\n" "$expected_hex"
    return 1
  fi
}

# Standard tx fields used by the cases below.
ALICE='"hex:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"'
R32='"hex:1111111111111111111111111111111111111111111111111111111111111111"'
S32='"hex:2222222222222222222222222222222222222222222222222222222222222222"'

FAILED=0
# Legacy pre-EIP-155: 9 fields → 6, no type prefix (prefix=0).
run_case "legacy_pre_eip155" \
  "[42, 1000000000, 21000, $ALICE, 1000000000000000000, \"\", 27, $R32, $S32]" \
  6 0 || FAILED=1

# EIP-2930 (type 1): 11 fields → 8, type prefix 0x01.
run_case "eip2930" \
  "[1, 42, 1000000000, 21000, $ALICE, 1000000000000000000, \"\", [], 1, $R32, $S32]" \
  8 1 || FAILED=1

# EIP-1559 (type 2): 12 fields → 9, type prefix 0x02.
run_case "eip1559" \
  "[1, 42, 1000000000, 2000000000, 21000, $ALICE, 1000000000000000000, \"\", [], 1, $R32, $S32]" \
  9 2 || FAILED=1

# EIP-4844 (type 3): 14 fields → 11, type prefix 0x03.
run_case "eip4844" \
  "[1, 42, 1000000000, 2000000000, 21000, $ALICE, 1000000000000000000, \"\", [], 1000000000, [\"hex:01abababababababababababababababababababababababababababababababab\"], 1, $R32, $S32]" \
  11 3 || FAILED=1

# EIP-7702 (type 4): 13 fields → 10, type prefix 0x04.
run_case "eip7702" \
  "[1, 42, 1000000000, 2000000000, 21000, $ALICE, 1000000000000000000, \"\", [], [[1, \"hex:dededededededededededededededededededede\", 0, 1, $R32, $S32]], 1, $R32, $S32]" \
  10 4 || FAILED=1

# Smoke: empty list (just to verify n=0 + prefix codepath).
run_case "empty_list_no_prefix" "[1, 2, 3]" 0 0 || FAILED=1
run_case "empty_list_prefix_02" "[1, 2, 3]" 0 2 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: tx_signing_hash matches keccak256(prefix || rlp([first n])) for all tx types"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
