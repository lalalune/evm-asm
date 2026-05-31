#!/usr/bin/env bash
# codegen-zisk-rlp-item-span-check.sh -- verify rlp_item_span returns the FULL
# encoded byte-span (start offset incl. prefix, total size) of list item i for
# every RLP item type (empty string, 32-byte hash-ref string, nested list,
# long string). This is the new primitive mpt_set needs for branch-slot
# reconstruction (bead evm-asm-fhsxz.4.1).
set -euo pipefail
cd "$(dirname "$0")/.."
REPO_ROOT="$(pwd)"

ZISKEMU="${ZISKEMU:-}"
if [[ -z "$ZISKEMU" ]]; then
  if command -v ziskemu >/dev/null 2>&1; then ZISKEMU="$(command -v ziskemu)"
  elif [[ -x "$HOME/.zisk/bin/ziskemu" ]]; then ZISKEMU="$HOME/.zisk/bin/ziskemu"
  else echo "ziskemu not found" >&2; exit 1; fi
fi

echo "==> lake build codegen"
lake build codegen >/dev/null
echo "==> emit zisk_rlp_item_span"
lake exe codegen --program zisk_rlp_item_span --halt linux93 -o "$REPO_ROOT/gen-out/zisk_rlp_item_span" >/dev/null

ZISKEMU="$ZISKEMU" uv run --directory execution-specs --quiet python3 - <<'PY'
import os, sys, struct, subprocess
sys.path.insert(0, "/home/zksecurity/evm-asm/scripts")
import mpt_ref as M  # rlp_bytes / rlp_list / rlp_len_prefix
ZISK = os.environ["ZISKEMU"]; ELF = "/home/zksecurity/evm-asm/gen-out/zisk_rlp_item_span.elf"

# A list whose 17 items span every shape a branch node can hold:
items_raw = [
    b"",                       # 0: empty  -> 0x80
    b"\x11" * 32,              # 1: 32-byte hash ref -> 0xa0 || hash
    None,                      # 2: nested list (inline node) -> 0xc.. list
    b"Z" * 60,                 # 3: long string (>=56) -> 0xb8 + len + bytes
    b"\x7f",                   # 4: single byte < 0x80 (raw)
    b"abc",                    # 5: short string
]
def enc(i):
    if i == 2:
        return M.rlp_list([M.rlp_bytes(b"x"), M.rlp_bytes(b"y")])  # inline node
    return M.rlp_bytes(items_raw[i])
encoded_items = [enc(i) for i in range(len(items_raw))]
payload = b"".join(encoded_items)
lst = M.rlp_len_prefix(len(payload), 0xC0) + payload
prefix_len = len(lst) - len(payload)

# expected (start, size) per index
starts, sizes = [], []
off = prefix_len
for e in encoded_items:
    starts.append(off); sizes.append(len(e)); off += len(e)

def run(i):
    body = struct.pack("<Q", len(lst)) + struct.pack("<Q", i) + lst
    body += b"\x00" * ((-len(body)) % 8)
    open("/home/zksecurity/evm-asm/gen-out/ris.in", "wb").write(body)
    subprocess.run([ZISK, "-e", ELF, "-i", "/home/zksecurity/evm-asm/gen-out/ris.in",
                    "-o", "/home/zksecurity/evm-asm/gen-out/ris.out", "-n", "2000000"],
                   check=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    o = open("/home/zksecurity/evm-asm/gen-out/ris.out", "rb").read()
    return struct.unpack_from("<q", o, 0)[0], struct.unpack_from("<Q", o, 8)[0], struct.unpack_from("<Q", o, 16)[0]

fail = 0
for i in range(len(encoded_items)):
    status, start, size = run(i)
    ok = (status == 0 and start == starts[i] and size == sizes[i])
    print(f"  item {i}: status={status} start={start}(exp {starts[i]}) size={size}(exp {sizes[i]})  {'OK' if ok else 'FAIL'}")
    if not ok: fail = 1
# out-of-range index -> status 1
status, _, _ = run(len(encoded_items))
print(f"  oob index: status={status} (exp 1)  {'OK' if status==1 else 'FAIL'}")
if status != 1: fail = 1
sys.exit(fail)
PY
rc=$?
[[ $rc -eq 0 ]] && echo "==> PASS: rlp_item_span matches reference for all item types" || echo "==> FAIL"
exit $rc
