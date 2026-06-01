#!/usr/bin/env bash
# codegen-zisk-extract-witness-state-section-check.sh -- verify
# extract_witness_state_section (bead evm-asm-fhsxz.2.4.2.2): locate the
# ExecutionWitness.state section within an SszStatelessInput.
#
# Python builds a STANDARD SSZ container (outer offset table -> witness at
# offsets[1]; witness inner offset table -> state at [0], codes at [1]) with a
# distinctive state section; the probe navigates SSZ_BASE -> outer[1] ->
# inner[0..1] and outputs the state section offset, length, and keccak. We
# verify all three against the reference (any wrong offset -> wrong keccak).
set -euo pipefail
cd "$(dirname "$0")/.."
REPO_ROOT="$(pwd)"

ZISKEMU="${ZISKEMU:-}"
if [[ -z "$ZISKEMU" ]]; then
  if command -v ziskemu >/dev/null 2>&1; then ZISKEMU="$(command -v ziskemu)"
  elif [[ -x "$HOME/.zisk/bin/ziskemu" ]]; then ZISKEMU="$HOME/.zisk/bin/ziskemu"
  else echo "ziskemu not found" >&2; exit 1; fi
fi

VDIR="$REPO_ROOT/gen-out/ssz-witness-state"
mkdir -p "$VDIR"

echo "==> build synthetic SszStatelessInput + expected state section"
uv run --directory execution-specs --quiet python3 - "$VDIR" <<'PY'
import sys, struct, os
from Crypto.Hash import keccak
VDIR = sys.argv[1]
def k(b):
    h = keccak.new(digest_bits=256); h.update(b); return h.digest()

# witness inner: 3 u32 offsets [state, codes, headers] then the 3 sections.
state   = b"".join(struct.pack("<I", 4) + bytes([i]) for i in range(20))  # distinctive
codes   = b"CODES-SECTION"
headers = b"HEADERS-SECTION-BYTES"
s_state = 12
s_codes = s_state + len(state)
s_head  = s_codes + len(codes)
witness = (struct.pack("<I", s_state) + struct.pack("<I", s_codes) + struct.pack("<I", s_head)
           + state + codes + headers)

# outer: 4 u32 offsets [npr, witness, chain_config, public_keys] then sections.
npr = b"NEW-PAYLOAD-REQUEST-PLACEHOLDER"; cfg = b"CHAIN-CONFIG"; pk = b"PUBKEYS"
o0 = 16; o1 = o0 + len(npr); o2 = o1 + len(witness); o3 = o2 + len(cfg)
outer = (struct.pack("<I", o0) + struct.pack("<I", o1) + struct.pack("<I", o2) + struct.pack("<I", o3)
         + npr + witness + cfg + pk)

# the probe's SSZ_BASE = input start; the blob maps to INPUT+8 directly.
body = bytearray(outer)
while len(body) % 8: body.append(0)
with open(os.path.join(VDIR, "ws.input"), "wb") as f:
    f.write(bytes(body))

# expected: state offset from SSZ_BASE = o1 (witness) + s_state; len = len(state); keccak(state)
exp_off = o1 + s_state
with open(os.path.join(VDIR, "ws.expected"), "w") as f:
    f.write(f"{exp_off} {len(state)} {k(state).hex()}\n")
print(f"witness@{o1} state@(witness+{s_state}) => off={exp_off} len={len(state)} kc={k(state).hex()[:16]}..")
PY

echo "==> lake build codegen"
lake build codegen >/dev/null

echo "==> emit zisk_extract_witness_state_section probe ELF"
lake exe codegen --program zisk_extract_witness_state_section --halt linux93 \
  -o "$REPO_ROOT/gen-out/zisk_extract_witness_state_section"

out="$VDIR/ws.output"
"$ZISKEMU" -e "$REPO_ROOT/gen-out/zisk_extract_witness_state_section.elf" -i "$VDIR/ws.input" \
  -o "$out" -n 2000000 >/dev/null 2>&1 </dev/null || { echo "  ERROR (ziskemu)"; exit 1; }
act_off="$(od -An -tu8 -j 0 -N 8 "$out" | tr -d ' \n')"
act_len="$(od -An -tu8 -j 8 -N 8 "$out" | tr -d ' \n')"
act_kc="$(xxd -p -s 16 -l 32 "$out" | tr -d '\n')"
read exp_off exp_len exp_kc < "$VDIR/ws.expected"
if [[ "$act_off" == "$exp_off" && "$act_len" == "$exp_len" && "$act_kc" == "$exp_kc" ]]; then
  echo "  PASS   off=$act_off len=$act_len keccak=$act_kc"
  echo "==> PASS: extract_witness_state_section matches reference"
else
  echo "  FAIL"
  echo "    off exp=$exp_off act=$act_off ; len exp=$exp_len act=$act_len"
  echo "    keccak exp=$exp_kc"; echo "    keccak act=$act_kc"
  echo "==> FAIL"; exit 1
fi
