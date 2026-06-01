#!/usr/bin/env bash
# codegen-zisk-step2-verdict-check.sh -- verify the Step-2 verdict composition
# (bead evm-asm-fhsxz.2.4.2 core): block_header_ssz_to_rlp + validate_header_rlp_pair
# + withdrawals_state_root + memcmp -> the successful_validation bit.
#
# Builds a CONSISTENT withdrawal-only block: a pre-state trie + withdrawals
# (reusing the validated mpt_ref withdrawal-recompute vector), a valid parent
# header (state_root = pre-state root), and a `this` SSZ payload whose
# state_root = the post-state root and whose header is a valid child of the
# parent. Expects verdict=1. Then tampers `this.state_root` -> expects 0.
set -euo pipefail
cd "$(dirname "$0")/.."
REPO_ROOT="$(pwd)"

ZISKEMU="${ZISKEMU:-}"
if [[ -z "$ZISKEMU" ]]; then
  if command -v ziskemu >/dev/null 2>&1; then ZISKEMU="$(command -v ziskemu)"
  elif [[ -x "$HOME/.zisk/bin/ziskemu" ]]; then ZISKEMU="$HOME/.zisk/bin/ziskemu"
  else echo "ziskemu not found" >&2; exit 1; fi
fi

VDIR="$REPO_ROOT/gen-out/step2-verdict"
mkdir -p "$VDIR"

echo "==> build consistent valid + tampered scenarios"
uv run --directory execution-specs --quiet python3 - "$VDIR" "$REPO_ROOT/scripts" <<'PY'
import sys, struct, os
VDIR, SCRIPTS = sys.argv[1], sys.argv[2]
sys.path.insert(0, SCRIPTS)
import mpt_ref as m
import rlp
from Crypto.Hash import keccak
def k(b):
    h = keccak.new(digest_bits=256); h.update(b); return h.digest()
EMPTY_OMMER = bytes.fromhex("1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347")
EMPTY_TRIE  = bytes.fromhex("56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421")

# state side: pre-state trie + withdrawals -> post-state root (validated vector)
v = m.vec_withdrawals_state_root()
pre_root = v["root"]; post_root = v["expected"]
witness = m.ssz_section(v["witness"]); wds = v["wds"]

GL, BF, N, T = 30_000_000, 1_000_000_000, 100, 1_700_000_000
coinbase, receipts = b"\x33" * 20, b"\x66" * 32
bloom = bytes(range(256)); prev_randao = b"\x77" * 32
extra = b"x"; nonce8 = b"\x00" * 8
wd_root, beacon, requests = b"\xbb" * 32, b"\xcc" * 32, b"\xdd" * 32
def ri(x):
    return b"" if x == 0 else x.to_bytes((x.bit_length() + 7) // 8, "big")

# parent header: 21-field canonical, state_root = pre_root, gas_used = gas_limit/2
parent = [b"\x11" * 32, EMPTY_OMMER, coinbase, pre_root, EMPTY_TRIE, receipts,
          bloom, ri(0), ri(N), ri(GL), ri(GL // 2), ri(T), extra, prev_randao,
          nonce8, ri(BF), wd_root, ri(0), ri(0), beacon, requests]
parent_rlp = rlp.encode(parent)
parent_hash = k(parent_rlp)

def payload_with_state_root(sr):
    f = bytearray(528)
    f[0:32] = parent_hash; f[32:52] = coinbase; f[52:84] = sr
    f[84:116] = receipts; f[116:372] = bloom; f[372:404] = prev_randao
    f[404:412] = (N + 1).to_bytes(8, "little"); f[412:420] = GL.to_bytes(8, "little")
    f[420:428] = (GL // 2).to_bytes(8, "little"); f[428:436] = (T + 12).to_bytes(8, "little")
    f[440:472] = BF.to_bytes(32, "little"); f[472:504] = b"\x99" * 32
    f[512:520] = (0).to_bytes(8, "little"); f[520:528] = (0).to_bytes(8, "little")
    eo = 528; to = 528 + len(extra)
    f[436:440] = eo.to_bytes(4, "little"); f[504:508] = to.to_bytes(4, "little")
    f[508:512] = to.to_bytes(4, "little")
    return bytes(f) + extra

def build(payload, name):
    body = bytearray()
    body += struct.pack("<Q", len(witness)) + struct.pack("<Q", len(wds))
    body += struct.pack("<Q", len(parent_rlp)) + struct.pack("<Q", len(payload))
    body += pre_root + EMPTY_TRIE + wd_root + beacon + requests   # parent_state_root, tx_root, wd_root, beacon, requests
    body += parent_rlp
    while len(body) % 8: body.append(0)
    body += payload
    while len(body) % 8: body.append(0)
    for wd in wds: body += struct.pack("<Q", len(wd))
    for wd in wds:
        body += wd
        while len(body) % 8: body.append(0)
    body += witness
    while len(body) % 8: body.append(0)
    with open(os.path.join(VDIR, name + ".input"), "wb") as fh:
        fh.write(bytes(body))

build(payload_with_state_root(post_root), "valid")          # state_root matches -> verdict 1
build(payload_with_state_root(b"\xee" * 32), "tampered")    # wrong state_root -> verdict 0
print(f"pre_root={pre_root.hex()[:16]}.. post_root={post_root.hex()[:16]}.. parent_hash={parent_hash.hex()[:16]}..")
PY

echo "==> lake build codegen"
lake build codegen >/dev/null

echo "==> emit zisk_step2_verdict probe ELF"
lake exe codegen --program zisk_step2_verdict --halt linux93 \
  -o "$REPO_ROOT/gen-out/zisk_step2_verdict"

run() { "$ZISKEMU" -e "$REPO_ROOT/gen-out/zisk_step2_verdict.elf" -i "$VDIR/$1.input" \
    -o "$VDIR/$1.output" -n 15000000 >/dev/null 2>&1 </dev/null \
    && od -An -tu8 -j 0 -N 8 "$VDIR/$1.output" | tr -d ' \n' || echo ERR; }
fail=0
v="$(run valid)";   [[ "$v" == "1" ]] && echo "  PASS   valid    verdict=$v" || { echo "  FAIL   valid    verdict=$v (want 1)"; fail=1; }
t="$(run tampered)";[[ "$t" == "0" ]] && echo "  PASS   tampered verdict=$t" || { echo "  FAIL   tampered verdict=$t (want 0)"; fail=1; }
[[ "$fail" -eq 0 ]] && echo "==> PASS: step2 verdict composition produces the correct successful_validation bit" \
  || { echo "==> FAIL"; exit 1; }
