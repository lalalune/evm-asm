#!/usr/bin/env bash
# Verify mpt_delete_acc deletion slices: single-leaf deletion, branch-only
# deletion without canonical collapse, and covered branch-collapse cases.
set -euo pipefail
cd "$(dirname "$0")/.."
REPO_ROOT="$(pwd)"

ZISKEMU="${ZISKEMU:-}"
if [[ -z "$ZISKEMU" ]]; then
  if command -v ziskemu >/dev/null 2>&1; then ZISKEMU="$(command -v ziskemu)"
  elif [[ -x "$HOME/.zisk/bin/ziskemu" ]]; then ZISKEMU="$HOME/.zisk/bin/ziskemu"
  else echo "ziskemu not found" >&2; exit 1; fi
fi

VDIR="$REPO_ROOT/gen-out/mpt-delete-acc"
mkdir -p "$VDIR"
echo "==> generate delete-acc vectors"
uv run --directory execution-specs --quiet python3 - "$VDIR" <<'PY'
from __future__ import annotations
import struct, sys
from Crypto.Hash import keccak

outdir = sys.argv[1]

def k256(b: bytes) -> bytes:
    h = keccak.new(digest_bits=256); h.update(b); return h.digest()

def rlp_len_prefix(length: int, base: int) -> bytes:
    if length < 56:
        return bytes([base + length])
    bl = length.to_bytes((length.bit_length() + 7) // 8, "big")
    return bytes([base + 55 + len(bl)]) + bl

def rlp_bytes(b: bytes) -> bytes:
    if len(b) == 1 and b[0] < 0x80:
        return b
    return rlp_len_prefix(len(b), 0x80) + b

def rlp_list(items: list[bytes]) -> bytes:
    payload = b"".join(items)
    return rlp_len_prefix(len(payload), 0xC0) + payload

def hp_encode(nibbles: list[int], is_leaf: bool) -> bytes:
    flag = (2 if is_leaf else 0) + (1 if len(nibbles) % 2 else 0)
    out = bytearray()
    if len(nibbles) % 2 == 1:
        out.append(flag * 16 + nibbles[0]); nibbles = nibbles[1:]
    else:
        out.append(flag * 16)
    for i in range(0, len(nibbles), 2):
        out.append(nibbles[i] * 16 + nibbles[i + 1])
    return bytes(out)

def leaf_node(path: list[int], value: bytes) -> bytes:
    return rlp_list([rlp_bytes(hp_encode(path, True)), rlp_bytes(value)])

def branch_node(slots: list[bytes], value: bytes = b"") -> bytes:
    return rlp_list(slots + [rlp_bytes(value)])

def node_ref(node: bytes) -> bytes:
    return node if len(node) < 32 else b"\xa0" + k256(node)

def trie_root(node: bytes) -> bytes:
    return k256(node)

EMPTY_TRIE_ROOT = bytes.fromhex("56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421")

def ssz_section(elements: list[bytes]) -> bytes:
    out = bytearray(); off = 4 * len(elements)
    for e in elements:
        out += struct.pack("<I", off); off += len(e)
    for e in elements:
        out += e
    return bytes(out)

def build_input(root_hash: bytes, path: list[int], witness: list[bytes]) -> bytes:
    body = bytearray()
    sec = ssz_section(witness)
    body += struct.pack("<Q", len(sec))
    body += struct.pack("<Q", len(path))
    body += root_hash
    body += bytes(path)
    while len(body) % 8:
        body += b"\x00"
    body += sec
    while len(body) % 8:
        body += b"\x00"
    return bytes(body)

def write_case(name: str, root_hash: bytes, path: list[int], witness: list[bytes], expected: bytes, status: int = 0) -> None:
    with open(f"{outdir}/{name}.input", "wb") as f:
        f.write(build_input(root_hash, path, witness))
    with open(f"{outdir}/{name}.expected", "w") as f:
        f.write(expected.hex())
    with open(f"{outdir}/{name}.status", "w") as f:
        f.write(str(status))

leaf = leaf_node([1, 2, 3, 4], b"old-value")
write_case("leaf_to_empty", trie_root(leaf), [1, 2, 3, 4], [leaf], EMPTY_TRIE_ROOT)

la = leaf_node([0xa, 0xb], b"A" * 32)
lb = leaf_node([0xc, 0xd], b"B" * 32)
lc = leaf_node([0xe, 0xf], b"C" * 32)
slots = [b"\x80"] * 16
slots[1] = node_ref(la); slots[2] = node_ref(lb); slots[3] = node_ref(lc)
root = branch_node(slots)
slots2 = list(slots); slots2[1] = b"\x80"
root2 = branch_node(slots2)
write_case("branch_no_collapse", trie_root(root), [1, 0xa, 0xb], [root, la], trie_root(root2))

slots3 = [b"\x80"] * 16
slots3[1] = node_ref(la); slots3[2] = node_ref(lb)
root3 = branch_node(slots3)
collapsed = leaf_node([2, 0xc, 0xd], b"B" * 32)
write_case("branch_collapse_leaf", trie_root(root3), [1, 0xa, 0xb], [root3, la, lb], trie_root(collapsed))

slots4 = [b"\x80"] * 16
slots4[1] = node_ref(la)
root4 = branch_node(slots4, b"branch-value")
collapsed_value = leaf_node([], b"branch-value")
write_case("branch_value_collapse", trie_root(root4), [1, 0xa, 0xb], [root4, la], trie_root(collapsed_value))
PY

echo "==> lake build codegen"
lake build codegen >/dev/null

echo "==> emit zisk_mpt_delete_acc probe ELF"
lake exe codegen --program zisk_mpt_delete_acc --halt linux93 \
  -o "$REPO_ROOT/gen-out/zisk_mpt_delete_acc"

read_u64() { od -An -tu8 -j "$2" -N 8 "$1" | tr -d ' \n'; }

fail=0
for name in leaf_to_empty branch_no_collapse branch_collapse_leaf branch_value_collapse; do
  out="$VDIR/$name.output"
  if ! "$ZISKEMU" -e "$REPO_ROOT/gen-out/zisk_mpt_delete_acc.elf" \
        -i "$VDIR/$name.input" -o "$out" -n 10000000 >/dev/null 2>&1 </dev/null; then
    echo "  ERROR  $name (ziskemu)"; fail=1; continue
  fi
  exp="$(cat "$VDIR/$name.expected")"
  exp_status="$(cat "$VDIR/$name.status")"
  act="$(od -An -tx1 -N 32 "$out" | tr -d ' \n')"
  st="$(read_u64 "$out" 32)"
  if [[ "$st" == "$exp_status" ]] && { [[ "$exp_status" != "0" ]] || [[ "$act" == "$exp" ]]; }; then
    echo "  PASS   $name"
  else
    echo "  FAIL   $name"
    echo "      root expected $exp"
    echo "      root actual   $act"
    echo "      status        $st (expected $exp_status)"
    fail=1
  fi
done

[[ "$fail" -eq 0 ]] && echo "==> PASS: mpt_delete_acc vectors match Python roots" \
  || { echo "==> FAIL"; exit 1; }
