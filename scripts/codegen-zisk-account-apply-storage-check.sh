#!/usr/bin/env bash
# codegen-zisk-account-apply-storage-check.sh -- verify account_apply_storage_slot
# (bead fhsxz.2.4.2.5 step c) against the Python MPT reference, incl. the REAL
# EIP-2935 history-contract genesis write derived from an eip4895 fixture.
set -euo pipefail
cd "$(dirname "$0")/.."
REPO_ROOT="$(pwd)"
ZISKEMU="${ZISKEMU:-}"
if [[ -z "$ZISKEMU" ]]; then
  if command -v ziskemu >/dev/null 2>&1; then ZISKEMU="$(command -v ziskemu)"
  elif [[ -x "$HOME/.zisk/bin/ziskemu" ]]; then ZISKEMU="$HOME/.zisk/bin/ziskemu"
  else echo "ziskemu not found" >&2; exit 1; fi
fi
VDIR="$REPO_ROOT/gen-out/aps"; mkdir -p "$VDIR"
echo "==> build + emit probe"
lake build codegen >/dev/null
lake exe codegen --program zisk_account_apply_storage_slot --halt linux93 -o "$REPO_ROOT/gen-out/zisk_account_apply_storage_slot" >/dev/null

uv run --directory execution-specs --quiet python3 - "$VDIR" "$REPO_ROOT/scripts" <<'PY'
import sys, os, struct
VDIR, SCRIPTS = sys.argv[1], sys.argv[2]
sys.path.insert(0, SCRIPTS)
import mpt_ref as m
import rlp
EMPTY=bytes.fromhex("56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421")
def nib(b):
    o=[]
    for x in b: o+=[x>>4,x&0xf]
    return o
def srss(slot, val):
    # storage-trie leaf value is RLP(word); leaf_node wraps it again
    return m.trie_root(m.leaf_node(nib(m.k256(slot)), rlp.encode(val)))
def pack(acct, slot, val):
    # file: [0:8]acct_len [8:16]val_len [16:48]slot [48:80]val [128:]acct
    body=bytearray(struct.pack("<Q",len(acct))+struct.pack("<Q",len(val)))
    body+=slot; body+=val.ljust(32,b"\x00")  # slot(32)+val padded to 32 -> ends at 80
    body+=b"\x00"*(128-len(body))
    body+=acct
    while len(body)%8: body.append(0)
    return bytes(body)
cases=[]
# 1) EIP-2935-style: empty-storage contract, write slot 0 -> 32-byte parentHash
ph=b"\x5d"*32
acct=rlp.encode([b"\x01", b"", EMPTY, b"\xba"*32])
new_sr=srss(b"\x00"*32, ph)
exp=rlp.encode([b"\x01", b"", new_sr, b"\xba"*32])
cases.append(("eip2935_slot0", acct, b"\x00"*32, ph, 0, exp))
# 2) EIP-4788-style: empty-storage contract, write slot 12 -> word 0x0c
acct2=rlp.encode([b"\x01", b"", EMPTY, b"\xcc"*32])
new_sr2=srss((12).to_bytes(32,"big"), b"\x0c")
exp2=rlp.encode([b"\x01", b"", new_sr2, b"\xcc"*32])
cases.append(("eip4788_slot12", acct2, (12).to_bytes(32,"big"), b"\x0c", 0, exp2))
# 3) conservative: NON-empty prior storage -> status 1
acct3=rlp.encode([b"\x01", b"", b"\xb1"*32, b"\xba"*32])
cases.append(("nonempty_conservative", acct3, b"\x00"*32, ph, 1, b""))
for name,acct,slot,val,status,exp in cases:
    open(f"{VDIR}/{name}.input","wb").write(pack(acct,slot,val))
    open(f"{VDIR}/{name}.expected","w").write(f"{status} {exp.hex()}\n")
print("wrote", len(cases), "cases")
PY

fail=0
for f in "$VDIR"/*.input; do
  b="${f%.input}"; out="$b.out"
  "$ZISKEMU" -e gen-out/zisk_account_apply_storage_slot.elf -i "$f" -o "$out" -n 20000000 >/dev/null 2>&1 </dev/null
  st="$(od -An -tu8 -j 0 -N 8 "$out"|tr -d ' \n')"
  olen="$(od -An -tu8 -j 8 -N 8 "$out"|tr -d ' \n')"
  got=""; [[ "$olen" -gt 0 && "$olen" -lt 250 ]] && got="$(xxd -p -s 16 -l "$olen" "$out"|tr -d '\n')"
  read exp_st exp_hex < "$b.expected"
  name="$(basename "$b")"
  if [[ "$exp_st" == "1" ]]; then
    [[ "$st" == "1" ]] && echo "  PASS $name (conservative status=1)" || { echo "  FAIL $name status=$st want 1"; fail=1; }
  else
    if [[ "$st" == "0" && "$got" == "$exp_hex" ]]; then echo "  PASS $name (new account len=$olen)"
    else echo "  FAIL $name status=$st len=$olen"; echo "    got=$got"; echo "    exp=$exp_hex"; fail=1; fi
  fi
done
[[ "$fail" -eq 0 ]] && echo "==> PASS: account_apply_storage_slot matches the Python MPT reference" || { echo "==> FAIL"; exit 1; }
