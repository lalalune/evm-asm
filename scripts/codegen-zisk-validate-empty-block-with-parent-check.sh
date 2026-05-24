#!/usr/bin/env bash
# codegen-zisk-validate-empty-block-with-parent-check.sh -- PR-K183.
#
# Composite: header-pair invariants (K174) + empty-block check (K182).
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

echo "==> emit zisk_validate_empty_block_with_parent ELF"
lake exe codegen --program zisk_validate_empty_block_with_parent --halt linux93 \
  -o gen-out/zisk_validate_empty_block_with_parent

REPO_ROOT="$(pwd)"

EMPTY_TRIE_ROOT="56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421"
EMPTY_OMMERS_HASH="1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347"

# run_case <name> <break: 'none' | 'pair_number' | 'tx_root' | 'body_tx'>
#         <exp_status> <exp_valid>
run_case() {
  local name="$1" brk="$2" exp_status="$3" exp_valid="$4"

  local in_file="$REPO_ROOT/gen-out/zisk_validate_empty_block_with_parent_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_validate_empty_block_with_parent_${name}.output"

  uv run --directory execution-specs --quiet python3 -c "
import struct, sys, rlp
try:
    from Crypto.Hash import keccak
    def keccak256(b):
        h = keccak.new(digest_bits=256); h.update(b); return h.digest()
except Exception:
    import sha3
    def keccak256(b): return sha3.keccak_256(b).digest()

def u_be(n):
    if n == 0: return b''
    return n.to_bytes((n.bit_length() + 7) // 8, 'big')

brk = '$brk'
EMPTY_TRIE_ROOT = bytes.fromhex('$EMPTY_TRIE_ROOT')
EMPTY_OMMERS_HASH = bytes.fromhex('$EMPTY_OMMERS_HASH')
BAD = b'\\xff'*32

# Parent: arbitrary, with empty-block-style root fields too.
parent_fields = [
    b'\\xa1'*32, EMPTY_OMMERS_HASH, b'\\xa3'*20, b'\\xa4'*32, EMPTY_TRIE_ROOT,
    EMPTY_TRIE_ROOT, b'\\x00'*256, b'', u_be(100), u_be(30000000),
    b'\\x82\\x02\\x00', u_be(1000), b'', b'\\xa7'*32, b'\\x00'*8,
    b'\\x82\\x12\\x34', EMPTY_TRIE_ROOT,
]
parent_rlp = rlp.encode(parent_fields)
parent_hash = keccak256(parent_rlp)

# Child: empty block by default, broken per <brk>
child_num = 101 if brk != 'pair_number' else 102
tx_root  = BAD if brk == 'tx_root' else EMPTY_TRIE_ROOT

child_fields = [
    parent_hash, EMPTY_OMMERS_HASH, b'\\xb3'*20, b'\\xb4'*32, tx_root,
    EMPTY_TRIE_ROOT, b'\\x00'*256, b'', u_be(child_num), u_be(30000000),
    b'\\x82\\x02\\x00', u_be(1001), b'', b'\\xb7'*32, b'\\x00'*8,
    b'\\x82\\x12\\x34', EMPTY_TRIE_ROOT,
]
child_rlp = rlp.encode(child_fields)

tx_body = [b'\\xaa'*10] if brk == 'body_tx' else []
body_rlp = rlp.encode([tx_body, [], []])

with open(sys.argv[1], 'wb') as f:
    record = struct.pack('<Q', len(parent_rlp)) + \
             struct.pack('<Q', len(child_rlp)) + \
             struct.pack('<Q', len(body_rlp)) + \
             parent_rlp + child_rlp + body_rlp
    f.write(record)
    pad = (-len(record)) % 8
    if pad: f.write(b'\x00' * pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_validate_empty_block_with_parent.elf \
    -i "$in_file" -o "$out_file" -n 5000000 \
    >"$REPO_ROOT/gen-out/zisk_validate_empty_block_with_parent_${name}.emu.log" 2>&1 || true

  local status_le; status_le="$(xxd -p -l 8 "$out_file" | tr -d '\n')"
  local valid_le;  valid_le="$( dd if="$out_file" bs=1 skip=8 count=8 2>/dev/null | xxd -p | tr -d '\n')"
  local status valid
  status="$(python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$status_le'))[0])")"
  valid="$( python3 -c "import struct; print(struct.unpack('<Q', bytes.fromhex('$valid_le'))[0])")"

  if [[ "$status" == "$exp_status" && "$valid" == "$exp_valid" ]]; then
    printf "  %-30s OK   status=%s valid=%s\n" "$name" "$status" "$valid"
    return 0
  else
    printf "  %-30s FAIL status=%s/exp%s valid=%s/exp%s\n" \
      "$name" "$status" "$exp_status" "$valid" "$exp_valid"
    return 1
  fi
}

FAILED=0
run_case "all_match"              "none"        0 1 || FAILED=1
run_case "fail_pair_number"       "pair_number" 0 0 || FAILED=1
run_case "fail_empty_tx_root"     "tx_root"     0 0 || FAILED=1
run_case "fail_body_has_tx"       "body_tx"     0 0 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: validate_empty_block_with_parent enforces pair + empty invariants jointly"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
