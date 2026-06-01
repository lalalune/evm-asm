#!/usr/bin/env bash
# codegen-zisk-bal-account-post-fields-check.sh -- verify bal_account_post_fields.
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
echo "==> generate BAL post-field vectors"
python3 - "$VDIR" <<'PYGEN'
import os
import struct
import sys

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


def change_pair(index: int, value: bytes) -> bytes:
    return rlp_list([rlp_int(index), value])


def bal_account_change_rlp(address: bytes, balance_changes=None, nonce_changes=None):
    balance_changes = balance_changes or []
    nonce_changes = nonce_changes or []
    bc = [change_pair(i, rlp_int(v)) for i, v in balance_changes]
    nc = [change_pair(i, rlp_int(v)) for i, v in nonce_changes]
    return rlp_list([rlp_bytes(address), rlp_list([]), rlp_list([]),
                     rlp_list(bc), rlp_list(nc), rlp_list([])])


def build_input(account_change: bytes) -> bytes:
    body = struct.pack("<Q", len(account_change)) + account_change
    while len(body) % 8 != 0:
        body += b"\x00"
    return body


absent = (1 << 64) - 1
cases = [
    ("bpf_absent", bytes.fromhex("00112233445566778899aabbccddeeff00112233"), {}, absent, b"", absent, b""),
    ("bpf_balance_nonce", bytes.fromhex("c0f6dc9e5836f54caadbf59cc69346c508e1992b"),
     dict(balance_changes=[(1, 5), (2, 10 ** 10)], nonce_changes=[(1, 1)]),
     len(minimal_be(10 ** 10)), minimal_be(10 ** 10), 1, b"\x01"),
    ("bpf_nonce_only", bytes.fromhex("0000000000000000000000000000000000000001"),
     dict(nonce_changes=[(7, 0), (9, 2)]), absent, b"", 1, b"\x02"),
    ("bpf_zero_balance", bytes.fromhex("0000000000000000000000000000000000000002"),
     dict(balance_changes=[(1, 0)]), 0, b"", absent, b""),
]

for name, addr, kwargs, bal_len, bal, nonce_len, nonce in cases:
    account_change = bal_account_change_rlp(addr, **kwargs)
    with open(f"{outdir}/{name}.input", "wb") as f:
        f.write(build_input(account_change))
    bal_hex = bal.hex() if bal else "-"
    nonce_hex = nonce.hex() if nonce else "-"
    with open(f"{outdir}/{name}.expected", "w") as f:
        f.write("\t".join([str(bal_len), bal_hex, str(nonce_len), nonce_hex]))
    print(f"{name:18} balance_len={bal_len} nonce_len={nonce_len}")
PYGEN

echo "==> lake build codegen"
lake build codegen >/dev/null

echo "==> emit zisk_bal_account_post_fields probe ELF"
lake exe codegen --program zisk_bal_account_post_fields --halt linux93 \
  -o "$REPO_ROOT/gen-out/zisk_bal_account_post_fields"

fail=0
for name in bpf_absent bpf_balance_nonce bpf_nonce_only bpf_zero_balance; do
  out="$VDIR/$name.output"
  "$ZISKEMU" -e "$REPO_ROOT/gen-out/zisk_bal_account_post_fields.elf" \
    -i "$VDIR/$name.input" -o "$out" -n 2000000 >/dev/null 2>&1 </dev/null \
    || { echo "  ERROR  $name"; fail=1; continue; }
  status="$(od -An -tu8 -j 0 -N 8 "$out" | tr -d ' \n')"
  bal_len="$(od -An -tu8 -j 8 -N 8 "$out" | tr -d ' \n')"
  nonce_len="$(od -An -tu8 -j 48 -N 8 "$out" | tr -d ' \n')"
  IFS=$'\t' read -r exp_bal_len exp_bal exp_nonce_len exp_nonce < "$VDIR/$name.expected" || true
  [[ "$exp_bal" == "-" ]] && exp_bal=""
  [[ "$exp_nonce" == "-" ]] && exp_nonce=""
  bal=""
  if [[ "$bal_len" != "18446744073709551615" && "$bal_len" != "0" ]]; then
    bal="$(xxd -p -s 16 -l "$bal_len" "$out" | tr -d '\n')"
  fi
  nonce=""
  if [[ "$nonce_len" != "18446744073709551615" && "$nonce_len" != "0" ]]; then
    nonce="$(xxd -p -s 56 -l "$nonce_len" "$out" | tr -d '\n')"
  fi
  if [[ "$status" == "0" && "$bal_len" == "$exp_bal_len" && "$bal" == "$exp_bal" && "$nonce_len" == "$exp_nonce_len" && "$nonce" == "$exp_nonce" ]]; then
    echo "  PASS   $name  bal_len=$bal_len nonce_len=$nonce_len"
  else
    echo "  FAIL   $name status=$status"
    echo "    expected: bal_len=$exp_bal_len bal=$exp_bal nonce_len=$exp_nonce_len nonce=$exp_nonce"
    echo "    actual:   bal_len=$bal_len bal=$bal nonce_len=$nonce_len nonce=$nonce"
    fail=1
  fi
done
[[ "$fail" -eq 0 ]] && echo "==> PASS: bal_account_post_fields matches reference" \
  || { echo "==> FAIL"; exit 1; }
