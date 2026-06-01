#!/usr/bin/env bash
# codegen-zisk-bal-account-state-root-check.sh -- verify BAL account replay into mpt_state_root_ins.
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
echo "==> generate BAL account state-root vector"
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


def account_rlp(nonce: int, balance: int) -> bytes:
    # Compact account-shaped value for a small one-leaf state trie probe.
    return rlp_list([rlp_int(nonce), rlp_int(balance), rlp_bytes(b""), rlp_bytes(b"")])


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
    # Leaf, even-length 64-nibble account path: flags byte 0x20 then packed path.
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


def build_input(root_hash, witness, bal_list, accounts, flags):
    body = bytearray()
    body += struct.pack("<QQQ", len(witness), len(accounts), len(bal_list))
    body += root_hash
    for account, flag in zip(accounts, flags):
        body += struct.pack("<QQ", len(account), flag)
    for account in accounts:
        body += account
        align8_body(body)
    body += bal_list
    align8_body(body)
    body += witness
    align8_body(body)
    return bytes(body)


addr = bytes.fromhex("c0f6dc9e5836f54caadbf59cc69346c508e1992b")
old_account = account_rlp(1, 5)
new_account = account_rlp(1, 10 ** 10)
path = account_path(addr)
old_leaf = leaf_node(path, old_account)
new_leaf = leaf_node(path, new_account)
root_hash = keccak256(old_leaf)
expected = keccak256(new_leaf)
bal_list = rlp_list([account_change(addr, balance_changes=[(1, 10 ** 10)])])
with open(f"{outdir}/basr_modify.input", "wb") as f:
    f.write(build_input(root_hash, ssz_section([old_leaf]), bal_list, [old_account], [0]))
with open(f"{outdir}/basr_modify.expected", "w") as f:
    f.write(expected.hex())
print(f"basr_modify root={root_hash.hex()[:16]}.. expected={expected.hex()[:16]}..")
PYGEN

echo "==> lake build codegen"
lake build codegen >/dev/null

echo "==> emit zisk_bal_account_state_root probe ELF"
lake exe codegen --program zisk_bal_account_state_root --halt linux93 \
  -o "$REPO_ROOT/gen-out/zisk_bal_account_state_root"

out="$VDIR/basr_modify.output"
"$ZISKEMU" -e "$REPO_ROOT/gen-out/zisk_bal_account_state_root.elf" \
  -i "$VDIR/basr_modify.input" -o "$out" -n 12000000 >/dev/null 2>&1 </dev/null
status="$(od -An -tu8 -j 32 -N 8 "$out" | tr -d ' \n')"
actual="$(xxd -p -s 0 -l 32 "$out" | tr -d '\n')"
expected="$(cat "$VDIR/basr_modify.expected")"
if [[ "$status" == "0" && "$actual" == "$expected" ]]; then
  echo "  PASS   basr_modify root=${actual:0:16}.."
  echo "==> PASS: bal_account_state_root matches reference"
else
  echo "  FAIL   basr_modify status=$status"
  echo "    expected: $expected"
  echo "    actual:   $actual"
  echo "==> FAIL"
  exit 1
fi
