#!/usr/bin/env bash
# codegen-zisk-runtime-selfdestruct-account-inputs-check.sh
#
# Validate the runtime SELFDESTRUCT account-input loader against the optional
# account-witness context produced by scripts/pack-bytecode.py.
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

RUN_DIR="${RUN_DIR:-gen-out/runtime_selfdestruct_account_inputs}"
case "$RUN_DIR" in
  /*) ;;
  *) RUN_DIR="$PWD/$RUN_DIR" ;;
esac
mkdir -p "$RUN_DIR" gen-out

echo "==> lake build codegen"
lake build codegen

echo "==> emit runtime_selfdestruct_account_inputs ELF"
lake exe codegen --program runtime_selfdestruct_account_inputs \
  --halt linux93 \
  -o gen-out/runtime_selfdestruct_account_inputs

make_case() {
  local name="$1" address="$2" nonce="$3" balance="$4" code_hex="$5"
  uv run --directory execution-specs --quiet python3 - "$RUN_DIR/$name" "$address" "$nonce" "$balance" "$code_hex" <<'INNERPY'
import struct, sys
from pathlib import Path
import rlp
from Crypto.Hash import keccak

out = Path(sys.argv[1])
address = bytes.fromhex(sys.argv[2])
nonce, balance = int(sys.argv[3]), int(sys.argv[4])
code = bytes.fromhex(sys.argv[5])

def k256(b):
    h = keccak.new(digest_bits=256); h.update(b); return h.digest()

def hp_encode(nibbles, is_leaf):
    flag = 2 if is_leaf else 0
    if len(nibbles) % 2 == 1:
        flag |= 1
        result = bytes([flag * 0x10 + nibbles[0]])
        nibbles = nibbles[1:]
    else:
        result = bytes([flag * 0x10])
    for i in range(0, len(nibbles), 2):
        result += bytes([nibbles[i] * 0x10 + nibbles[i + 1]])
    return result

def bytes_to_nibbles(b):
    out = []
    for byte in b:
        out.extend([byte >> 4, byte & 0xf])
    return out

def leaf_node(path_nibbles, value):
    return rlp.encode([hp_encode(path_nibbles, True), value])

def build_ssz_section(elements):
    section = b''
    offset = 4 * len(elements)
    for e in elements:
        section += struct.pack('<I', offset)
        offset += len(e)
    return section + b''.join(elements)

def encode_header(state_root):
    fields = [
        b'\x11'*32, b'\x22'*32, b'\x33'*20, state_root, b'\x55'*32,
        b'\x66'*32, b'\x00'*256, b'', b'\x01', b'\x83\xff\xff\xff',
        b'', b'\x83\x01\x02\x03', b'', b'\x77'*32, b'\x00'*8,
    ]
    return rlp.encode(fields)

EMPTY_TRIE = bytes.fromhex('56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421')

account = rlp.encode([nonce, balance, EMPTY_TRIE, k256(code)])
path = bytes_to_nibbles(k256(address))
leaf = leaf_node(path, account)
state_root = k256(leaf)
header = encode_header(state_root)
witness_state = build_ssz_section([leaf])

expected = (
    struct.pack('<Q', 0) +
    struct.pack('<Q', len(account)) +
    struct.pack('<Q', len(account)) +
    struct.pack('<Q', 32) +
    struct.pack('<Q', 0) +
    struct.pack('<Q', len(account)) +
    struct.pack('<Q', len(account)) +
    b'\0' * 8 +
    account.ljust(96, b'\0') +
    account.ljust(96, b'\0')
)

out.mkdir(parents=True, exist_ok=True)
out.joinpath('header.bin').write_bytes(header)
out.joinpath('state.bin').write_bytes(witness_state)
out.joinpath('expected.bin').write_bytes(expected)
out.joinpath('beneficiary.csv').write_text(', '.join(f'0x{x:02x}' for x in address))
INNERPY
}

ALICE="$(printf 'aa%.0s' $(seq 1 20))"
FAILED=0

make_case same_account "$ALICE" 7 11 "6001600201"

for name in same_account; do
  echo "==> pack $name"
  scripts/pack-bytecode.py \
    --env "address=0x$ALICE" \
    --state-header-rlp "@$RUN_DIR/$name/header.bin" \
    --witness-state "@$RUN_DIR/$name/state.bin" \
    "$(cat "$RUN_DIR/$name/beneficiary.csv")" \
    "$RUN_DIR/$name/input.bin"

  echo "==> ziskemu $name"
  if ! "$ZISKEMU" -e gen-out/runtime_selfdestruct_account_inputs.elf \
    -i "$RUN_DIR/$name/input.bin" \
    -o "$RUN_DIR/$name/output.bin" \
    -n 5000000 \
    >"$RUN_DIR/$name/emu.log" 2>&1; then
    FAILED=1
  fi

  actual="$(xxd -p -l 256 "$RUN_DIR/$name/output.bin" 2>/dev/null | tr -d '\n')"
  expected="$(xxd -p -l 256 "$RUN_DIR/$name/expected.bin" | tr -d '\n')"
  if [[ "$actual" == "$expected" ]]; then
    printf "  %-12s OK\n" "$name"
  else
    printf "  %-12s FAIL\n    expected: %s\n    actual:   %s\n" "$name" "$expected" "$actual"
    FAILED=1
  fi
done

if [[ "$FAILED" -ne 0 ]]; then
  echo "==> FAIL: runtime SELFDESTRUCT account inputs" >&2
  exit 1
fi

echo "==> PASS: runtime SELFDESTRUCT account inputs"
