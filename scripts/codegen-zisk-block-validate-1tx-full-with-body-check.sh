#!/usr/bin/env bash
# codegen-zisk-block-validate-1tx-full-with-body-check.sh -- PR-K190.
#
# Body-aware single-call validator for 1-tx blocks.
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

echo "==> emit zisk_block_validate_1tx_full_with_body ELF"
lake exe codegen --program zisk_block_validate_1tx_full_with_body --halt linux93 \
  -o gen-out/zisk_block_validate_1tx_full_with_body

REPO_ROOT="$(pwd)"

# run_case <name> <break_pair 0/1> <break_tx_root 0/1> <break_body 0/1>
#                 <exp_status> <exp_valid>
run_case() {
  local name="$1" bp="$2" btr="$3" bb="$4" exp_status="$5" exp_valid="$6"

  local in_file="$REPO_ROOT/gen-out/zisk_block_validate_1tx_full_with_body_${name}.input"
  local out_file="$REPO_ROOT/gen-out/zisk_block_validate_1tx_full_with_body_${name}.output"

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

bp = $bp == 1
btr = $btr == 1
bb = $bb == 1

tx0 = bytes.fromhex('f8500184ee6b280082520894aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa881bc16d674ec80000801ba01111111111111111111111111111111111111111111111111111111111111111a02222222222222222222222222222222222222222222222222222222222222222')

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

correct_tx_root = keccak256(hp_leaf([8, 0], tx0))

parent_rlp = rlp.encode([
    b'\\xa1'*32, b'\\xa2'*32, b'\\xa3'*20, b'\\xa4'*32, b'\\xa5'*32,
    b'\\xa6'*32, b'\\x00'*256, b'', u_be(100), u_be(30000000),
    b'\\x82\\x02\\x00', u_be(1000), b'', b'\\xa7'*32, b'\\x00'*8,
    b'\\x82\\x12\\x34',
])
parent_hash = keccak256(parent_rlp)

field4 = b'\\xff'*32 if btr else correct_tx_root
child_num = 102 if bp else 101
child_rlp = rlp.encode([
    parent_hash, b'\\xb2'*32, b'\\xb3'*20, b'\\xb4'*32, field4,
    b'\\xb6'*32, b'\\x00'*256, b'', u_be(child_num), u_be(30000000),
    b'\\x82\\x02\\x00', u_be(1001), b'', b'\\xb7'*32, b'\\x00'*8,
    b'\\x82\\x12\\x34',
])

if bb:
    body_rlp = rlp.encode([[tx0, tx0], [], []])  # 2 txs -> count fail
else:
    body_rlp = rlp.encode([[tx0], [], []])

with open(sys.argv[1], 'wb') as f:
    record = struct.pack('<Q', len(parent_rlp)) + \
             struct.pack('<Q', len(child_rlp)) + \
             struct.pack('<Q', len(body_rlp)) + \
             parent_rlp + child_rlp + body_rlp
    f.write(record)
    pad = (-len(record)) % 8
    if pad: f.write(b'\x00' * pad)
" "$in_file"

  "$ZISKEMU" -e gen-out/zisk_block_validate_1tx_full_with_body.elf \
    -i "$in_file" -o "$out_file" -n 10000000 \
    >"$REPO_ROOT/gen-out/zisk_block_validate_1tx_full_with_body_${name}.emu.log" 2>&1 || true

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

FAILED=0
run_case "all_match"          0 0 0  0 1 || FAILED=1
run_case "fail_pair"          1 0 0  0 0 || FAILED=1
run_case "fail_tx_root"       0 1 0  0 0 || FAILED=1
run_case "fail_body_count"    0 0 1  3 0 || FAILED=1

echo
if [[ $FAILED -eq 0 ]]; then
  echo "==> PASS: block_validate_1tx_full_with_body validates body + header + tx_root"
  exit 0
else
  echo "==> FAIL"
  exit 1
fi
