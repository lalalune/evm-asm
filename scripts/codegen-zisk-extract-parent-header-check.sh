#!/usr/bin/env bash
# codegen-zisk-extract-parent-header-check.sh -- verify
# extract_parent_header_and_state_root (bead evm-asm-fhsxz.2.4.2.4): find the
# parent header in the witness headers list (keccak == this.parent_hash) and
# extract its state_root.
#
# Python builds a synthetic StatelessInput whose witness.headers section is an
# SSZ List[ByteList] of two RLP headers [h1, parent]; this.parent_hash =
# keccak256(parent). The probe navigates -> witness_lookup_by_hash -> finds
# parent -> header_extract_state_root (field 3). We verify status, parent
# header length, and the extracted state_root.
set -euo pipefail
cd "$(dirname "$0")/.."
REPO_ROOT="$(pwd)"

ZISKEMU="${ZISKEMU:-}"
if [[ -z "$ZISKEMU" ]]; then
  if command -v ziskemu >/dev/null 2>&1; then ZISKEMU="$(command -v ziskemu)"
  elif [[ -x "$HOME/.zisk/bin/ziskemu" ]]; then ZISKEMU="$HOME/.zisk/bin/ziskemu"
  else echo "ziskemu not found" >&2; exit 1; fi
fi

VDIR="$REPO_ROOT/gen-out/ssz-parent-header"
mkdir -p "$VDIR"

echo "==> build synthetic StatelessInput (witness.headers = [h1, parent])"
uv run --directory execution-specs --quiet python3 - "$VDIR" "$REPO_ROOT/scripts" <<'PY'
import sys, struct, os
VDIR, SCRIPTS = sys.argv[1], sys.argv[2]
sys.path.insert(0, SCRIPTS)
import mpt_ref as m            # ssz_section, k256
import rlp
u32 = lambda x: struct.pack("<I", x)

# two RLP headers; field 3 = state_root. parent is the one we look up.
sr1     = b"\x44" * 32
parent_sr = b"\xab" * 32
h1     = rlp.encode([b"\x0a" * 32, b"\x0b" * 32, b"\x0c" * 20, sr1, b"\x0d"])
parent = rlp.encode([b"\x1a" * 32, b"\x1b" * 32, b"\x1c" * 20, parent_sr, b"\x1e"])
parent_hash = m.k256(parent)

# witness.headers = SSZ List[ByteList] of [h1, parent]
headers = m.ssz_section([h1, parent])
state = b"S" * 8; codes = b"C" * 8
s_state = 12; s_codes = s_state + len(state); s_head = s_codes + len(codes)
witness = u32(s_state) + u32(s_codes) + u32(s_head) + state + codes + headers

# outer: [npr, witness, chain_config, public_keys]
npr = b"NPR"; cfg = b"CFG"; pk = b"PK"
o0 = 16; o1 = o0 + len(npr); o2 = o1 + len(witness); o3 = o2 + len(cfg)
outer = u32(o0) + u32(o1) + u32(o2) + u32(o3) + npr + witness + cfg + pk

# input: parent_hash(32) then the SSZ blob (SSZ_BASE = INPUT+40)
body = bytearray(parent_hash + outer)
while len(body) % 8: body.append(0)
with open(os.path.join(VDIR, "ph.input"), "wb") as f:
    f.write(bytes(body))
with open(os.path.join(VDIR, "ph.expected"), "w") as f:
    f.write(f"{len(parent)} {parent_sr.hex()}\n")
print(f"parent_len={len(parent)} parent_state_root={parent_sr.hex()[:16]}.. parent_hash={parent_hash.hex()[:16]}..")
PY

echo "==> lake build codegen"
lake build codegen >/dev/null

echo "==> emit zisk_extract_parent_header_and_state_root probe ELF"
lake exe codegen --program zisk_extract_parent_header_and_state_root --halt linux93 \
  -o "$REPO_ROOT/gen-out/zisk_extract_parent_header_and_state_root"

out="$VDIR/ph.output"
"$ZISKEMU" -e "$REPO_ROOT/gen-out/zisk_extract_parent_header_and_state_root.elf" -i "$VDIR/ph.input" \
  -o "$out" -n 3000000 >/dev/null 2>&1 </dev/null || { echo "  ERROR (ziskemu)"; exit 1; }
status="$(od -An -tu8 -j 0 -N 8 "$out" | tr -d ' \n')"
hlen="$(od -An -tu8 -j 8 -N 8 "$out" | tr -d ' \n')"
sr="$(xxd -p -s 16 -l 32 "$out" | tr -d '\n')"
read exp_len exp_sr < "$VDIR/ph.expected"
if [[ "$status" == "0" && "$hlen" == "$exp_len" && "$sr" == "$exp_sr" ]]; then
  echo "  PASS   status=0 parent_len=$hlen state_root=$sr"
  echo "==> PASS: extract_parent_header_and_state_root matches reference"
else
  echo "  FAIL   status=$status (want 0); len exp=$exp_len act=$hlen"
  echo "    state_root exp=$exp_sr"; echo "    state_root act=$sr"
  echo "==> FAIL"; exit 1
fi
