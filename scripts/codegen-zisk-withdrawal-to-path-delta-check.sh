#!/usr/bin/env bash
# codegen-zisk-withdrawal-to-path-delta-check.sh -- verify withdrawal_to_path_delta
# (bead evm-asm-fhsxz.2.2.1) against the Python reference.
#
# withdrawal_to_path_delta turns a Shanghai+ withdrawal RLP into the two
# inputs the state-trie balance credit needs: the account key path
# (bytes_to_nibbles(keccak256(address))) and the wei delta (amount_gwei * 1e9
# as 32-byte BE). The probe writes path @ OUTPUT+8 (64 nibble bytes) and
# delta @ OUTPUT+72 (32 bytes); we diff both against mpt_ref.py.
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
echo "==> generate vectors via the validated Python reference"
uv run --directory execution-specs --quiet python3 "$REPO_ROOT/scripts/mpt_ref.py" "$VDIR"

echo "==> lake build codegen"
lake build codegen >/dev/null

echo "==> emit zisk_withdrawal_to_path_delta probe ELF"
lake exe codegen --program zisk_withdrawal_to_path_delta --halt linux93 \
  -o "$REPO_ROOT/gen-out/zisk_withdrawal_to_path_delta"

fail=0
for name in wtpd1 wtpd2 wtpd3; do
  out="$VDIR/$name.output"
  "$ZISKEMU" -e "$REPO_ROOT/gen-out/zisk_withdrawal_to_path_delta.elf" \
    -i "$VDIR/$name.input" -o "$out" -n 3000000 >/dev/null 2>&1 </dev/null \
    || { echo "  ERROR  $name"; fail=1; continue; }
  act_path="$(xxd -p -s 8 -l 64 "$out" | tr -d '\n')"
  act_delta="$(xxd -p -s 72 -l 32 "$out" | tr -d '\n')"
  exp_path="$(cat "$VDIR/$name.path")"
  exp_delta="$(cat "$VDIR/$name.delta")"
  if [[ "$act_path" == "$exp_path" && "$act_delta" == "$exp_delta" ]]; then
    echo "  PASS   $name  delta=$act_delta"
  else
    echo "  FAIL   $name"
    [[ "$act_path"  != "$exp_path"  ]] && { echo "    path exp: $exp_path"; echo "    path act: $act_path"; }
    [[ "$act_delta" != "$exp_delta" ]] && { echo "    delta exp: $exp_delta"; echo "    delta act: $act_delta"; }
    fail=1
  fi
done
[[ "$fail" -eq 0 ]] && echo "==> PASS: withdrawal_to_path_delta matches reference" \
  || { echo "==> FAIL"; exit 1; }
