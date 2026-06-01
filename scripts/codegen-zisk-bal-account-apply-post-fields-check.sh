#!/usr/bin/env bash
# codegen-zisk-bal-account-apply-post-fields-check.sh -- verify BAL account post-field account RLP rewriting.
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
echo "==> generate BAL account apply-post-field vectors"
python3 - "$VDIR" <<'PYGEN'
import os
import struct
import sys

outdir = sys.argv[1]
os.makedirs(outdir, exist_ok=True)

EMPTY_ROOT = bytes.fromhex("56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421")
EMPTY_CODE_HASH = bytes.fromhex("c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470")
SLOT_1_VALUE_7_ROOT = bytes.fromhex("2e7827dc2c61c322f13f77e6f25dd18844ccc48426dde70301d2d57d138fced8")
SLOTS_1_2_VALUES_7_9_ROOT = bytes.fromhex("d4768ae8d8aaa8da763864dd76573bdc5d107ac968eb886393419033cc66dac7")


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


def account_rlp(nonce: int, balance: int, storage_root: bytes = EMPTY_ROOT) -> bytes:
    return rlp_list([rlp_int(nonce), rlp_int(balance), rlp_bytes(storage_root), rlp_bytes(EMPTY_CODE_HASH)])


def change_pair(index: int, value: bytes) -> bytes:
    return rlp_list([rlp_int(index), value])


def storage_change(slot: int, changes) -> bytes:
    return rlp_list([rlp_int(slot), rlp_list([change_pair(i, rlp_int(v)) for i, v in changes])])


def bal_account_change_rlp(address: bytes, storage_changes=None, balance_changes=None, nonce_changes=None):
    storage_changes = storage_changes or []
    balance_changes = balance_changes or []
    nonce_changes = nonce_changes or []
    sc = [storage_change(slot, changes) for slot, changes in storage_changes]
    bc = [change_pair(i, rlp_int(v)) for i, v in balance_changes]
    nc = [change_pair(i, rlp_int(v)) for i, v in nonce_changes]
    return rlp_list([rlp_bytes(address), rlp_list(sc), rlp_list([]),
                     rlp_list(bc), rlp_list(nc), rlp_list([])])


def build_input(account: bytes, account_change: bytes) -> bytes:
    body = struct.pack("<QQ", len(account), len(account_change)) + account
    while len(body) % 8 != 0:
        body += b"\x00"
    body += account_change
    while len(body) % 8 != 0:
        body += b"\x00"
    return body


addr = bytes.fromhex("c0f6dc9e5836f54caadbf59cc69346c508e1992b")
base = account_rlp(1, 5)
cases = [
    ("baap_noop", base, bal_account_change_rlp(addr), base),
    ("baap_balance", base, bal_account_change_rlp(addr, balance_changes=[(1, 10 ** 10)]), account_rlp(1, 10 ** 10)),
    ("baap_nonce", base, bal_account_change_rlp(addr, nonce_changes=[(1, 7)]), account_rlp(7, 5)),
    ("baap_both", base, bal_account_change_rlp(addr, balance_changes=[(1, 9)], nonce_changes=[(1, 7)]), account_rlp(7, 9)),
    ("baap_zero_balance", base, bal_account_change_rlp(addr, balance_changes=[(1, 0)]), account_rlp(1, 0)),
    (
        "baap_storage_only",
        base,
        bal_account_change_rlp(addr, storage_changes=[(1, [(1, 7)])]),
        account_rlp(1, 5, SLOT_1_VALUE_7_ROOT),
    ),
    (
        "baap_two_storage",
        base,
        bal_account_change_rlp(addr, storage_changes=[(1, [(1, 7)]), (2, [(2, 9)])]),
        account_rlp(1, 5, SLOTS_1_2_VALUES_7_9_ROOT),
    ),
]

for name, account, account_change, expected in cases:
    with open(f"{outdir}/{name}.input", "wb") as f:
        f.write(build_input(account, account_change))
    with open(f"{outdir}/{name}.expected", "w") as f:
        f.write(expected.hex())
    print(f"{name:18} account_len={len(account)} expected_len={len(expected)}")
PYGEN

echo "==> lake build codegen"
lake build codegen >/dev/null

echo "==> emit zisk_bal_account_apply_post_fields probe ELF"
lake exe codegen --program zisk_bal_account_apply_post_fields --halt linux93 \
  -o "$REPO_ROOT/gen-out/zisk_bal_account_apply_post_fields"

fail=0
for name in baap_noop baap_balance baap_nonce baap_both baap_zero_balance baap_storage_only baap_two_storage; do
  out="$VDIR/$name.output"
  "$ZISKEMU" -e "$REPO_ROOT/gen-out/zisk_bal_account_apply_post_fields.elf" \
    -i "$VDIR/$name.input" -o "$out" -n 2000000 >/dev/null 2>&1 </dev/null \
    || { echo "  ERROR  $name"; fail=1; continue; }
  status="$(od -An -tu8 -j 248 -N 8 "$out" | tr -d ' \n')"
  got_len="$(od -An -tu8 -j 0 -N 8 "$out" | tr -d ' \n')"
  expected="$(cat "$VDIR/$name.expected")"
  got="$(xxd -p -s 8 -l "$got_len" "$out" | tr -d '\n')"
  exp_len=$(( ${#expected} / 2 ))
  if [[ "$status" == "0" && "$got_len" == "$exp_len" && "$got" == "$expected" ]]; then
    echo "  PASS   $name  len=$got_len"
  else
    echo "  FAIL   $name status=$status"
    echo "    expected: len=$exp_len rlp=$expected"
    echo "    actual:   len=$got_len rlp=$got"
    fail=1
  fi
done
[[ "$fail" -eq 0 ]] && echo "==> PASS: bal_account_apply_post_fields matches reference" \
  || { echo "==> FAIL"; exit 1; }
