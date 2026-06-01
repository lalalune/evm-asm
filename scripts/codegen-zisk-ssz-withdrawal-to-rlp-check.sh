#!/usr/bin/env bash
# codegen-zisk-ssz-withdrawal-to-rlp-check.sh -- verify ssz_withdrawal_to_rlp
# (bead evm-asm-fhsxz.2.4.2.1): SSZ Withdrawal (44B) -> withdrawal RLP.
#
# Python builds an SSZ Withdrawal (index|validator_index|address|amount, all
# little-endian fixed fields) + the canonical RLP rlp([index, validator_index,
# address, amount]); the probe reads the 44-byte SSZ withdrawal and emits the
# RLP; we diff byte-for-byte over several cases.
set -euo pipefail
cd "$(dirname "$0")/.."
REPO_ROOT="$(pwd)"

ZISKEMU="${ZISKEMU:-}"
if [[ -z "$ZISKEMU" ]]; then
  if command -v ziskemu >/dev/null 2>&1; then ZISKEMU="$(command -v ziskemu)"
  elif [[ -x "$HOME/.zisk/bin/ziskemu" ]]; then ZISKEMU="$HOME/.zisk/bin/ziskemu"
  else echo "ziskemu not found" >&2; exit 1; fi
fi

VDIR="$REPO_ROOT/gen-out/ssz-withdrawal"
mkdir -p "$VDIR"

echo "==> build SSZ withdrawals + expected RLP"
uv run --directory execution-specs --quiet python3 - "$VDIR" <<'PY'
import sys, struct, os
import rlp
VDIR = sys.argv[1]
def ri(x):
    return b"" if x == 0 else x.to_bytes((x.bit_length() + 7) // 8, "big")
# (name, index, validator_index, address, amount_gwei)
cases = [
    ("w1", 0, 0, b"\x11" * 20, 1),
    ("w2", 7, 99, bytes.fromhex("00112233445566778899aabbccddeeff00112233"), 32 * 10**9),
    ("w3", 2**63, 2**40, b"\xab" * 20, 2**48),
]
for name, idx, vidx, addr, amt in cases:
    ssz = struct.pack("<Q", idx) + struct.pack("<Q", vidx) + addr + struct.pack("<Q", amt)
    assert len(ssz) == 44
    body = ssz                                     # the 44B withdrawal maps to INPUT+8
    body += b"\x00" * ((-len(body)) % 8)
    with open(os.path.join(VDIR, name + ".input"), "wb") as f:
        f.write(body)
    expected = rlp.encode([ri(idx), ri(vidx), addr, ri(amt)])
    with open(os.path.join(VDIR, name + ".expected"), "w") as f:
        f.write(expected.hex())
    print(f"{name}: rlp={expected.hex()}")
PY

echo "==> lake build codegen"
lake build codegen >/dev/null

echo "==> emit zisk_ssz_withdrawal_to_rlp probe ELF"
lake exe codegen --program zisk_ssz_withdrawal_to_rlp --halt linux93 \
  -o "$REPO_ROOT/gen-out/zisk_ssz_withdrawal_to_rlp"

fail=0
for name in w1 w2 w3; do
  out="$VDIR/$name.output"
  "$ZISKEMU" -e "$REPO_ROOT/gen-out/zisk_ssz_withdrawal_to_rlp.elf" -i "$VDIR/$name.input" \
    -o "$out" -n 2000000 >/dev/null 2>&1 </dev/null || { echo "  ERROR  $name"; fail=1; continue; }
  len="$(od -An -tu8 -j 0 -N 8 "$out" | tr -d ' \n')"
  actual="$(xxd -p -s 8 -l "$len" "$out" | tr -d '\n')"
  expected="$(cat "$VDIR/$name.expected")"
  if [[ "$actual" == "$expected" ]]; then echo "  PASS   $name  $actual"
  else echo "  FAIL   $name"; echo "    exp: $expected"; echo "    act: $actual"; fail=1; fi
done
[[ "$fail" -eq 0 ]] && echo "==> PASS: ssz_withdrawal_to_rlp matches reference" || { echo "==> FAIL"; exit 1; }
