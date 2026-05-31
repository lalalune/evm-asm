#!/usr/bin/env bash
# codegen-zisk-storage-write-check.sh -- verify the storage-write primitives
# (bead evm-asm-fhsxz.2.4.2.5) against the Python MPT reference:
#   * storage_root_single_slot : storage_root of a 1-slot storage trie
#     (key = keccak(slot_key), value = rlp(minimal-BE word)).
#   * account_set_storage_root : replace field 2 (storageRoot) of an account RLP.
# Vectors mirror the EIP-2935 (slot 0 -> parentHash) and EIP-4788 (slot 0x0c ->
# small word) genesis writes plus a contract-account storage_root swap.
set -euo pipefail
cd "$(dirname "$0")/.."
REPO_ROOT="$(pwd)"
ZISKEMU="${ZISKEMU:-}"
if [[ -z "$ZISKEMU" ]]; then
  if command -v ziskemu >/dev/null 2>&1; then ZISKEMU="$(command -v ziskemu)"
  elif [[ -x "$HOME/.zisk/bin/ziskemu" ]]; then ZISKEMU="$HOME/.zisk/bin/ziskemu"
  else echo "ziskemu not found" >&2; exit 1; fi
fi
VDIR="$REPO_ROOT/gen-out/storage-write"; mkdir -p "$VDIR"

echo "==> build + emit probes"
lake build codegen >/dev/null
lake exe codegen --program zisk_storage_root_single_slot --halt linux93 -o "$REPO_ROOT/gen-out/zisk_storage_root_single_slot" >/dev/null
lake exe codegen --program zisk_account_set_storage_root --halt linux93 -o "$REPO_ROOT/gen-out/zisk_account_set_storage_root" >/dev/null

echo "==> generate vectors + expected (Python MPT reference)"
uv run --directory execution-specs --quiet python3 - "$VDIR" "$REPO_ROOT/scripts" <<'PY'
import sys, os, struct
VDIR, SCRIPTS = sys.argv[1], sys.argv[2]
sys.path.insert(0, SCRIPTS)
import mpt_ref as m
import rlp
def nibbles(b):
    out=[]
    for x in b: out += [x>>4, x&0xf]
    return out
def pad8(b):
    b=bytearray(b)
    while len(b)%8: b.append(0)
    return bytes(b)

# ---- storage_root_single_slot vectors ----
# slot_key is the 32-byte storage slot index; value is the minimal-BE stored word.
srss=[]
# EIP-2935-like: slot 0 -> 32-byte parent hash
srss.append((b"\x00"*32, b"\x5d"*32))
# EIP-4788-like: slot 0x0c -> word 0x0c (1 byte)
srss.append(((12).to_bytes(32,"big"), b"\x0c"))
# generic: slot 1 -> word 0x42
srss.append(((1).to_bytes(32,"big"), b"\x42"))
for i,(slot,val) in enumerate(srss):
    key=m.k256(slot)
    leaf=m.leaf_node(nibbles(key), val)
    root=m.trie_root(leaf)
    body=struct.pack("<Q", len(val)) + slot + val
    open(f"{VDIR}/srss_{i}.input","wb").write(pad8(body))
    open(f"{VDIR}/srss_{i}.expected","w").write(root.hex())

# ---- account_set_storage_root vectors ----
# account = rlp([nonce, balance, storageRoot, codeHash]); swap storageRoot.
asr=[]
acct1=rlp.encode([b"\x01", b"", b"\xb1"*32, b"\xba"*32])    # contract: nonce1 bal0
new1=b"\x56"*32
acct2=rlp.encode([b"\x02", b"\x05\x40", b"\x00"*32, b"\xcc"*32])
new2=b"\xab"*32
asr=[(acct1,new1),(acct2,new2)]
for i,(acct,new) in enumerate(asr):
    d=rlp.decode(acct)
    exp=rlp.encode([d[0], d[1], new, d[3]])
    body=struct.pack("<Q", len(acct)) + new + acct
    open(f"{VDIR}/asr_{i}.input","wb").write(pad8(body))
    open(f"{VDIR}/asr_{i}.expected","w").write(exp.hex())
print(f"wrote {len(srss)} srss + {len(asr)} asr vectors")
PY

fail=0
echo "==> storage_root_single_slot"
for f in "$VDIR"/srss_*.input; do
  b="${f%.input}"; out="$b.out"
  "$ZISKEMU" -e gen-out/zisk_storage_root_single_slot.elf -i "$f" -o "$out" -n 20000000 >/dev/null 2>&1 </dev/null
  got="$(xxd -p -s 0 -l 32 "$out"|tr -d '\n')"; exp="$(cat "$b.expected")"
  if [[ "$got" == "$exp" ]]; then echo "  PASS $(basename "$b") root=${got:0:16}.."
  else echo "  FAIL $(basename "$b") got=$got exp=$exp"; fail=1; fi
done
echo "==> account_set_storage_root"
for f in "$VDIR"/asr_*.input; do
  b="${f%.input}"; out="$b.out"
  "$ZISKEMU" -e gen-out/zisk_account_set_storage_root.elf -i "$f" -o "$out" -n 20000000 >/dev/null 2>&1 </dev/null
  olen="$(od -An -tu8 -j 0 -N 8 "$out"|tr -d ' \n')"
  got="$(xxd -p -s 8 -l "$olen" "$out"|tr -d '\n')"; exp="$(cat "$b.expected")"
  if [[ "$got" == "$exp" ]]; then echo "  PASS $(basename "$b") len=$olen"
  else echo "  FAIL $(basename "$b") got=$got exp=$exp"; fail=1; fi
done
[[ "$fail" -eq 0 ]] && echo "==> PASS: storage-write primitives match the Python MPT reference" || { echo "==> FAIL"; exit 1; }
