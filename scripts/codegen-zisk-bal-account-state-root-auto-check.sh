#!/usr/bin/env bash
# codegen-zisk-bal-account-state-root-auto-check.sh -- verify BAL replay with record derivation.
set -euo pipefail
cd "$(dirname "$0")/.."
REPO_ROOT="$(pwd)"

ZISKEMU="${ZISKEMU:-}"
if [[ -z "$ZISKEMU" ]]; then
  if command -v ziskemu >/dev/null 2>&1; then ZISKEMU="$(command -v ziskemu)"
  elif [[ -x "$HOME/.zisk/bin/ziskemu" ]]; then ZISKEMU="$HOME/.zisk/bin/ziskemu"
  else echo "ziskemu not found" >&2; exit 1; fi
fi

VDIR="$REPO_ROOT/gen-out/mpt-set"
echo "==> generate BAL account state-root auto vector"
uv run --directory execution-specs --quiet python3 - "$VDIR" <<'PYGEN'
import os
import struct
import sys
from ethereum.crypto.hash import keccak256

outdir = sys.argv[1]
os.makedirs(outdir, exist_ok=True)


def minimal_be(n: int) -> bytes:
    if n == 0:
        return b""
    return n.to_bytes((n.bit_length() + 7) // 8, "big")


def rlp_len_prefix(length: int, base: int) -> bytes:
    if length < 56:
        return bytes([base + length])
    l = minimal_be(length)
    return bytes([base + 55 + len(l)]) + l


def rlp_bytes(x: bytes) -> bytes:
    if len(x) == 1 and x[0] < 0x80:
        return x
    return rlp_len_prefix(len(x), 0x80) + x


def rlp_list(xs):
    payload = b"".join(xs)
    return rlp_len_prefix(len(payload), 0xc0) + payload


def rlp_int(n: int) -> bytes:
    return rlp_bytes(minimal_be(n))


EMPTY_TRIE = bytes.fromhex("56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421")
EMPTY_CODE = bytes.fromhex("c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470")


def account_rlp(nonce: int, balance: int) -> bytes:
    return rlp_list([rlp_int(nonce), rlp_int(balance), rlp_bytes(EMPTY_TRIE), rlp_bytes(EMPTY_CODE)])


def change_pair(index: int, value: bytes) -> bytes:
    return rlp_list([rlp_int(index), value])


def account_change(address: bytes, balance_changes=None, nonce_changes=None) -> bytes:
    balance_changes = balance_changes or []
    nonce_changes = nonce_changes or []
    bc = [change_pair(i, rlp_int(v)) for i, v in balance_changes]
    nc = [change_pair(i, rlp_int(v)) for i, v in nonce_changes]
    return rlp_list([rlp_bytes(address), rlp_list([]), rlp_list([]),
                     rlp_list(bc), rlp_list(nc), rlp_list([])])


def account_path(address: bytes) -> list[int]:
    out = []
    for b in keccak256(address):
        out.append(b >> 4)
        out.append(b & 0x0f)
    return out


def hp_encode(path: list[int], is_leaf: bool) -> bytes:
    flag = (2 if is_leaf else 0) + (1 if len(path) % 2 else 0)
    out = bytearray()
    if len(path) % 2:
        out.append(flag * 16 + path[0])
        path = path[1:]
    else:
        out.append(flag * 16)
    for i in range(0, len(path), 2):
        out.append(path[i] * 16 + path[i + 1])
    return bytes(out)


def leaf_node(path: list[int], value: bytes) -> bytes:
    return rlp_list([rlp_bytes(hp_encode(path, True)), rlp_bytes(value)])


def branch_node(slots: list[bytes], value: bytes = b"") -> bytes:
    return rlp_len_prefix(sum(len(slot) for slot in slots) + len(rlp_bytes(value)), 0xc0) + b"".join(slots) + rlp_bytes(value)


def node_ref(node: bytes) -> bytes:
    if len(node) < 32:
        return node
    return b"\xa0" + keccak256(node)


def ssz_section(elements):
    out = bytearray()
    off = 4 * len(elements)
    for element in elements:
        out += struct.pack("<I", off)
        off += len(element)
    for element in elements:
        out += element
    return bytes(out)


def align8_body(body: bytearray):
    while len(body) % 8 != 0:
        body += b"\x00"


def build_input(root_hash, witness, bal_list, n):
    body = bytearray()
    body += struct.pack("<QQQ", len(witness), n, len(bal_list))
    body += root_hash
    body += bal_list
    align8_body(body)
    body += witness
    align8_body(body)
    return bytes(body)


present_addr = bytes.fromhex("c0f6dc9e5836f54caadbf59cc69346c508e1992b")
present_path = account_path(present_addr)
for i in range(2, 256):
    missing_addr = i.to_bytes(20, "big")
    missing_path = account_path(missing_addr)
    if missing_path[0] != present_path[0]:
        break
else:
    raise AssertionError("could not find distinct first nibble")

old_account = account_rlp(1, 5)
present_new = account_rlp(1, 10 ** 10)
missing_new = account_rlp(7, 9)
old_leaf = leaf_node(present_path[1:], old_account)
present_leaf_new = leaf_node(present_path[1:], present_new)
missing_leaf_new = leaf_node(missing_path[1:], missing_new)

slots = [b"\x80"] * 16
slots[present_path[0]] = node_ref(old_leaf)
root = branch_node(slots)
root_hash = keccak256(root)

post_slots = list(slots)
post_slots[present_path[0]] = node_ref(present_leaf_new)
post_slots[missing_path[0]] = node_ref(missing_leaf_new)
expected = keccak256(branch_node(post_slots))

bal_list = rlp_list([
    account_change(present_addr, balance_changes=[(1, 10 ** 10)]),
    account_change(missing_addr, balance_changes=[(1, 9)], nonce_changes=[(1, 7)]),
])
with open(f"{outdir}/basra_modify_insert.input", "wb") as f:
    f.write(build_input(root_hash, ssz_section([root, old_leaf]), bal_list, 2))
with open(f"{outdir}/basra_modify_insert.expected", "w") as f:
    f.write(expected.hex())
print(f"basra_modify_insert slots={present_path[0]},{missing_path[0]} expected={expected.hex()[:16]}..")
PYGEN

echo "==> lake build codegen"
lake build codegen >/dev/null

echo "==> emit zisk_bal_account_state_root_auto probe ELF"
lake exe codegen --program zisk_bal_account_state_root_auto --halt linux93 \
  -o "$REPO_ROOT/gen-out/zisk_bal_account_state_root_auto"

out="$VDIR/basra_modify_insert.output"
"$ZISKEMU" -e "$REPO_ROOT/gen-out/zisk_bal_account_state_root_auto.elf" \
  -i "$VDIR/basra_modify_insert.input" -o "$out" -n 12000000 >/dev/null 2>&1 </dev/null
status="$(od -An -tu8 -j 32 -N 8 "$out" | tr -d ' \n')"
actual="$(xxd -p -s 0 -l 32 "$out" | tr -d '\n')"
expected="$(cat "$VDIR/basra_modify_insert.expected")"
if [[ "$status" == "0" && "$actual" == "$expected" ]]; then
  echo "  PASS   basra_modify_insert root=${actual:0:16}.."
  echo "==> PASS: bal_account_state_root_auto matches reference"
else
  echo "  FAIL   basra_modify_insert status=$status"
  echo "    expected: $expected"
  echo "    actual:   $actual"
  echo "==> FAIL"
  exit 1
fi
