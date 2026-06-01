#!/usr/bin/env bash
# codegen-zisk-bal-account-record-array-check.sh -- verify BAL pre-account record extraction.
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
echo "==> generate BAL account record-array vector"
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


def rlp_bytes(x: bytes) -> bytes:
    if len(x) == 1 and x[0] < 0x80:
        return x
    if len(x) <= 55:
        return bytes([0x80 + len(x)]) + x
    l = minimal_be(len(x))
    return bytes([0xb7 + len(l)]) + l + x


def rlp_list(xs):
    payload = b"".join(xs)
    if len(payload) <= 55:
        return bytes([0xc0 + len(payload)]) + payload
    l = minimal_be(len(payload))
    return bytes([0xf7 + len(l)]) + l + payload


def rlp_int(n: int) -> bytes:
    return rlp_bytes(minimal_be(n))


def account_rlp(nonce: int, balance: int, storage_root=None, code_hash=None) -> bytes:
    storage_root = storage_root or bytes.fromhex("56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421")
    code_hash = code_hash or bytes.fromhex("c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470")
    return rlp_list([rlp_int(nonce), rlp_int(balance), rlp_bytes(storage_root), rlp_bytes(code_hash)])


def change_pair(index: int, value: bytes) -> bytes:
    return rlp_list([rlp_int(index), value])


def account_change(address: bytes, balance_changes=None, nonce_changes=None) -> bytes:
    balance_changes = balance_changes or []
    nonce_changes = nonce_changes or []
    bc = [change_pair(i, rlp_int(v)) for i, v in balance_changes]
    nc = [change_pair(i, rlp_int(v)) for i, v in nonce_changes]
    return rlp_list([rlp_bytes(address), rlp_list([]), rlp_list([]),
                     rlp_list(bc), rlp_list(nc), rlp_list([])])


def account_path(address: bytes) -> bytes:
    out = bytearray()
    for b in keccak256(address):
        out.append(b >> 4)
        out.append(b & 0x0f)
    return bytes(out)


def hp_leaf(path):
    assert len(path) % 2 == 0
    out = bytearray([0x20])
    for i in range(0, len(path), 2):
        out.append((path[i] << 4) | path[i + 1])
    return bytes(out)


def leaf_node(path, value: bytes) -> bytes:
    return rlp_list([rlp_bytes(hp_leaf(path)), rlp_bytes(value)])


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
missing_addr = bytes.fromhex("0000000000000000000000000000000000000002")
old_account = account_rlp(1, 5)
empty_account = account_rlp(0, 0)
old_leaf = leaf_node(account_path(present_addr), old_account)
root_hash = keccak256(old_leaf)
bal_list = rlp_list([
    account_change(present_addr, balance_changes=[(1, 10 ** 10)]),
    account_change(missing_addr, balance_changes=[(1, 9)], nonce_changes=[(1, 7)]),
])
with open(f"{outdir}/bara_present_missing.input", "wb") as f:
    f.write(build_input(root_hash, ssz_section([old_leaf]), bal_list, 2))
with open(f"{outdir}/bara_present_missing.expected", "w") as f:
    f.write(old_account.hex() + "\n")
    f.write(empty_account.hex() + "\n")
print(f"bara_present_missing root={root_hash.hex()[:16]}.. lens={[len(old_account), len(empty_account)]}")
PYGEN

echo "==> lake build codegen"
lake build codegen >/dev/null

echo "==> emit zisk_bal_account_record_array probe ELF"
lake exe codegen --program zisk_bal_account_record_array --halt linux93 \
  -o "$REPO_ROOT/gen-out/zisk_bal_account_record_array"

out="$VDIR/bara_present_missing.output"
"$ZISKEMU" -e "$REPO_ROOT/gen-out/zisk_bal_account_record_array.elf" \
  -i "$VDIR/bara_present_missing.input" -o "$out" -n 4000000 >/dev/null 2>&1 </dev/null
status="$(od -An -tu8 -j 0 -N 8 "$out" | tr -d ' \n')"
mapfile -t expected < "$VDIR/bara_present_missing.expected"
fail=0
if [[ "$status" != "0" ]]; then
  echo "  FAIL   status=$status"
  fail=1
fi
arena_off=64
for i in 0 1; do
  desc_off=$((8 + 24 * i))
  ptr="$(od -An -tu8 -j "$desc_off" -N 8 "$out" | tr -d ' \n')"
  len="$(od -An -tu8 -j $((desc_off + 8)) -N 8 "$out" | tr -d ' \n')"
  flag="$(od -An -tu8 -j $((desc_off + 16)) -N 8 "$out" | tr -d ' \n')"
  expected_flag="$i"
  expected_ptr=$((0xa0010000 + arena_off))
  account="$(xxd -p -s "$arena_off" -l "$len" "$out" | tr -d '\n')"
  if [[ "$ptr" != "$expected_ptr" || "$flag" != "$expected_flag" || "$account" != "${expected[$i]}" ]]; then
    echo "  FAIL   row=$i ptr=$ptr len=$len flag=$flag"
    echo "    expected ptr=$expected_ptr flag=$expected_flag account=${expected[$i]}"
    echo "    actual account=$account"
    fail=1
  else
    echo "  PASS   row=$i len=$len flag=$flag"
  fi
  arena_off=$(( (arena_off + len + 7) & ~7 ))
done
[[ "$fail" -eq 0 ]] && echo "==> PASS: bal_account_record_array matches reference" \
  || { echo "==> FAIL"; exit 1; }
