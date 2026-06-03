#!/usr/bin/env bash
# codegen-zisk-runtime-sload-check.sh
#
# Validate runtime SLOAD cold-miss wiring through the account/storage witness
# context consumed by runtime_dispatcher.
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

RUN_DIR="${RUN_DIR:-gen-out/runtime_sload}"
case "$RUN_DIR" in
  /*) ;;
  *) RUN_DIR="$PWD/$RUN_DIR" ;;
esac
mkdir -p "$RUN_DIR" gen-out

echo "==> lake build codegen"
lake build codegen

echo "==> emit runtime_dispatcher ELF"
lake exe codegen --program runtime_dispatcher \
  --halt linux93 \
  -o gen-out/runtime_dispatcher

make_case() {
  local name="$1" mode="$2" lookup_addr="$3" stored_addr="$4" lookup_slot="$5" stored_slot="$6" slot_value="$7"
  uv run --directory execution-specs --quiet python3 - "$RUN_DIR/$name" "$mode" "$lookup_addr" "$stored_addr" "$lookup_slot" "$stored_slot" "$slot_value" <<'INNERPY'
import struct, sys
from pathlib import Path
import rlp
from Crypto.Hash import keccak

out = Path(sys.argv[1])
mode = sys.argv[2]
lookup_addr = bytes.fromhex(sys.argv[3])
stored_addr = bytes.fromhex(sys.argv[4])
lookup_slot = bytes.fromhex(sys.argv[5])
stored_slot = bytes.fromhex(sys.argv[6])
slot_value = int(sys.argv[7])

def k256(b):
    h = keccak.new(digest_bits=256)
    h.update(b)
    return h.digest()

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
    if not elements:
        return b""
    section = b""
    offset = 4 * len(elements)
    for e in elements:
        section += struct.pack("<I", offset)
        offset += len(e)
    return section + b"".join(elements)

def encode_header(state_root):
    fields = [
        b"\x11" * 32, b"\x22" * 32, b"\x33" * 20, state_root, b"\x55" * 32,
        b"\x66" * 32, b"\x00" * 256, b"", b"\x01", b"\x83\xff\xff\xff",
        b"", b"\x83\x01\x02\x03", b"", b"\x77" * 32, b"\x00" * 8,
    ]
    return rlp.encode(fields)

EMPTY_TRIE = bytes.fromhex("56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421")
EMPTY_CODE = bytes.fromhex("c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470")

def encode_account(nonce, balance, storage_root, code_hash):
    return rlp.encode([nonce, balance, storage_root, code_hash])

def build_storage_trie(slot_idx, value):
    leaf = leaf_node(bytes_to_nibbles(k256(slot_idx)), rlp.encode(value))
    return k256(leaf), build_ssz_section([leaf])

def build_state_trie(addr, account_rlp):
    leaf = leaf_node(bytes_to_nibbles(k256(addr)), account_rlp)
    return k256(leaf), build_ssz_section([leaf])

if mode == "present":
    storage_root, witness_storage = build_storage_trie(lookup_slot, slot_value)
    account = encode_account(0, 0, storage_root, EMPTY_CODE)
    state_root, witness_state = build_state_trie(lookup_addr, account)
    expected_value = slot_value.to_bytes(32, "big")[::-1]
elif mode == "slot_not_in_trie":
    storage_root, witness_storage = build_storage_trie(stored_slot, slot_value)
    account = encode_account(0, 0, storage_root, EMPTY_CODE)
    state_root, witness_state = build_state_trie(lookup_addr, account)
    expected_value = b"\x00" * 32
elif mode == "empty_storage":
    account = encode_account(0, 0, EMPTY_TRIE, EMPTY_CODE)
    state_root, witness_state = build_state_trie(lookup_addr, account)
    witness_storage = b""
    expected_value = b"\x00" * 32
elif mode == "missing_account":
    account = encode_account(0, 0, EMPTY_TRIE, EMPTY_CODE)
    state_root, witness_state = build_state_trie(stored_addr, account)
    witness_storage = b""
    expected_value = b"\x00" * 32
else:
    raise SystemExit("bad mode: " + mode)

header = encode_header(state_root)
bytecode = b"\x7f" + lookup_slot + b"\x54\x00"

out.mkdir(parents=True, exist_ok=True)
out.joinpath("header.bin").write_bytes(header)
out.joinpath("state.bin").write_bytes(witness_state)
out.joinpath("storage.bin").write_bytes(witness_storage)
out.joinpath("bytecode.csv").write_text(", ".join(f"0x{x:02x}" for x in bytecode))
out.joinpath("env.txt").write_text("address=0x" + lookup_addr.hex())
out.joinpath("expected.bin").write_bytes(expected_value)
INNERPY
}

ALICE="$(printf 'aa%.0s' $(seq 1 20))"
BOB="$(printf 'bb%.0s' $(seq 1 20))"
SLOT0="0000000000000000000000000000000000000000000000000000000000000000"
SLOT1="0000000000000000000000000000000000000000000000000000000000000001"
SLOT2="0000000000000000000000000000000000000000000000000000000000000002"

make_case present present "$ALICE" "$ALICE" "$SLOT0" "$SLOT0" 42
make_case slot_not_in_trie slot_not_in_trie "$ALICE" "$ALICE" "$SLOT2" "$SLOT1" 42
make_case empty_storage empty_storage "$ALICE" "$ALICE" "$SLOT0" "$SLOT0" 0
make_case missing_account missing_account "$BOB" "$ALICE" "$SLOT0" "$SLOT0" 0

FAILED=0
for name in present slot_not_in_trie empty_storage missing_account; do
  echo "==> pack $name"
  scripts/pack-bytecode.py \
    --env "$(cat "$RUN_DIR/$name/env.txt")" \
    --state-header-rlp "@$RUN_DIR/$name/header.bin" \
    --witness-state "@$RUN_DIR/$name/state.bin" \
    --witness-storage "@$RUN_DIR/$name/storage.bin" \
    "$(cat "$RUN_DIR/$name/bytecode.csv")" \
    "$RUN_DIR/$name/input.bin"

  echo "==> ziskemu $name"
  if ! "$ZISKEMU" -e gen-out/runtime_dispatcher.elf \
    -i "$RUN_DIR/$name/input.bin" \
    -o "$RUN_DIR/$name/output.bin" \
    -n 12000000 \
    >"$RUN_DIR/$name/emu.log" 2>&1; then
    FAILED=1
  fi

  actual="$(xxd -p -l 32 "$RUN_DIR/$name/output.bin" 2>/dev/null | tr -d '\n')"
  expected="$(xxd -p -l 32 "$RUN_DIR/$name/expected.bin" | tr -d '\n')"
  if [[ "$actual" == "$expected" ]]; then
    printf "  %-18s OK\n" "$name"
  else
    printf "  %-18s FAIL\n    expected: %s\n    actual:   %s\n" "$name" "$expected" "$actual"
    FAILED=1
  fi
done

echo "==> pack no_context"
scripts/pack-bytecode.py "$(cat "$RUN_DIR/present/bytecode.csv")" "$RUN_DIR/no_context.input"
"$ZISKEMU" -e gen-out/runtime_dispatcher.elf \
  -i "$RUN_DIR/no_context.input" \
  -o "$RUN_DIR/no_context.output" \
  -n 12000000 \
  >"$RUN_DIR/no_context.emu.log" 2>&1 || FAILED=1
actual="$(xxd -p -l 32 "$RUN_DIR/no_context.output" 2>/dev/null | tr -d '\n')"
expected="$(printf '00%.0s' $(seq 1 32))"
if [[ "$actual" == "$expected" ]]; then
  printf "  %-18s OK\n" "no_context"
else
  printf "  %-18s FAIL\n    expected: %s\n    actual:   %s\n" "no_context" "$expected" "$actual"
  FAILED=1
fi

echo "==> pack preloaded_log_wins"
scripts/pack-bytecode.py \
  --env "address=0x$ALICE" \
  --storage "(0x$SLOT0, 0x2b)" \
  --state-header-rlp "@$RUN_DIR/present/header.bin" \
  --witness-state "@$RUN_DIR/present/state.bin" \
  --witness-storage "@$RUN_DIR/present/storage.bin" \
  "$(cat "$RUN_DIR/present/bytecode.csv")" \
  "$RUN_DIR/preloaded_log_wins.input"
"$ZISKEMU" -e gen-out/runtime_dispatcher.elf \
  -i "$RUN_DIR/preloaded_log_wins.input" \
  -o "$RUN_DIR/preloaded_log_wins.output" \
  -n 12000000 \
  >"$RUN_DIR/preloaded_log_wins.emu.log" 2>&1 || FAILED=1
actual="$(xxd -p -l 32 "$RUN_DIR/preloaded_log_wins.output" 2>/dev/null | tr -d '\n')"
expected="2b$(printf '00%.0s' $(seq 1 31))"
if [[ "$actual" == "$expected" ]]; then
  printf "  %-18s OK\n" "preloaded_log_wins"
else
  printf "  %-18s FAIL\n    expected: %s\n    actual:   %s\n" "preloaded_log_wins" "$expected" "$actual"
  FAILED=1
fi

if [[ "$FAILED" -ne 0 ]]; then
  echo "==> FAIL: runtime SLOAD witness" >&2
  exit 1
fi

echo "==> PASS: runtime SLOAD witness"
