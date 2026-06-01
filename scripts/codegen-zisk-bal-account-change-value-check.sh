#!/usr/bin/env bash
# codegen-zisk-bal-account-change-value-check.sh -- verify BAL account path + post account value preparation.
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
echo "==> generate BAL account change path+value vectors"
uv run --directory execution-specs --quiet python3 - "$VDIR" <<'PYGEN'
import os
import struct
import sys
from ethereum.crypto.hash import keccak256

outdir = sys.argv[1]
os.makedirs(outdir, exist_ok=True)

EMPTY_ROOT = bytes.fromhex("56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421")
EMPTY_CODE_HASH = bytes.fromhex("c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470")


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
    return rlp_list([rlp_int(nonce), rlp_int(balance), rlp_bytes(EMPTY_ROOT), rlp_bytes(EMPTY_CODE_HASH)])


def change_pair(index: int, value: bytes) -> bytes:
    return rlp_list([rlp_int(index), value])


def bal_account_change_rlp(address: bytes, balance_changes=None, nonce_changes=None):
    balance_changes = balance_changes or []
    nonce_changes = nonce_changes or []
    bc = [change_pair(i, rlp_int(v)) for i, v in balance_changes]
    nc = [change_pair(i, rlp_int(v)) for i, v in nonce_changes]
    return rlp_list([rlp_bytes(address), rlp_list([]), rlp_list([]),
                     rlp_list(bc), rlp_list(nc), rlp_list([])])


def account_path(address: bytes) -> bytes:
    h = keccak256(address)
    out = bytearray()
    for b in h:
        out.append(b >> 4)
        out.append(b & 0x0f)
    return bytes(out)


def build_input(account: bytes, account_change: bytes) -> bytes:
    body = struct.pack("<QQ", len(account), len(account_change)) + account
    while len(body) % 8 != 0:
        body += b"\x00"
    body += account_change
    while len(body) % 8 != 0:
        body += b"\x00"
    return body


base = account_rlp(1, 5)
cases = [
    ("bacv_noop", bytes.fromhex("00112233445566778899aabbccddeeff00112233"), base, {}, base),
    ("bacv_balance", bytes.fromhex("c0f6dc9e5836f54caadbf59cc69346c508e1992b"), base,
     dict(balance_changes=[(1, 10 ** 10)]), account_rlp(1, 10 ** 10)),
    ("bacv_nonce", bytes.fromhex("0000000000000000000000000000000000000001"), base,
     dict(nonce_changes=[(1, 7)]), account_rlp(7, 5)),
    ("bacv_both", bytes.fromhex("0000000000000000000000000000000000000002"), base,
     dict(balance_changes=[(1, 9)], nonce_changes=[(1, 7)]), account_rlp(7, 9)),
]

for name, addr, account, kwargs, expected_value in cases:
    account_change = bal_account_change_rlp(addr, **kwargs)
    with open(f"{outdir}/{name}.input", "wb") as f:
        f.write(build_input(account, account_change))
    with open(f"{outdir}/{name}.path", "w") as f:
        f.write(account_path(addr).hex())
    with open(f"{outdir}/{name}.value", "w") as f:
        f.write(expected_value.hex())
    print(f"{name:14} path={account_path(addr).hex()[:16]}.. value_len={len(expected_value)}")
PYGEN

echo "==> lake build codegen"
lake build codegen >/dev/null

echo "==> emit zisk_bal_account_change_value probe ELF"
lake exe codegen --program zisk_bal_account_change_value --halt linux93 \
  -o "$REPO_ROOT/gen-out/zisk_bal_account_change_value"

fail=0
for name in bacv_noop bacv_balance bacv_nonce bacv_both; do
  out="$VDIR/$name.output"
  "$ZISKEMU" -e "$REPO_ROOT/gen-out/zisk_bal_account_change_value.elf" \
    -i "$VDIR/$name.input" -o "$out" -n 2000000 >/dev/null 2>&1 </dev/null \
    || { echo "  ERROR  $name"; fail=1; continue; }
  status="$(od -An -tu8 -j 0 -N 8 "$out" | tr -d ' \n')"
  actual_path="$(xxd -p -s 8 -l 64 "$out" | tr -d '\n')"
  value_len="$(od -An -tu8 -j 72 -N 8 "$out" | tr -d ' \n')"
  actual_value="$(xxd -p -s 80 -l "$value_len" "$out" | tr -d '\n')"
  expected_path="$(cat "$VDIR/$name.path")"
  expected_value="$(cat "$VDIR/$name.value")"
  expected_len=$(( ${#expected_value} / 2 ))
  if [[ "$status" == "0" && "$actual_path" == "$expected_path" && "$value_len" == "$expected_len" && "$actual_value" == "$expected_value" ]]; then
    echo "  PASS   $name  value_len=$value_len"
  else
    echo "  FAIL   $name status=$status"
    echo "    expected path=$expected_path len=$expected_len value=$expected_value"
    echo "    actual   path=$actual_path len=$value_len value=$actual_value"
    fail=1
  fi
done
[[ "$fail" -eq 0 ]] && echo "==> PASS: bal_account_change_value matches reference" \
  || { echo "==> FAIL"; exit 1; }
