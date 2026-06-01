#!/usr/bin/env bash
# codegen-zisk-mpt-state-root-check.sh -- verify the multi-change state-root
# recompute driver (bead evm-asm-fhsxz.4.3.2) against the Python reference.
#
# mpt_state_root threads mpt_set_acc over a list of value-only changes,
# accumulating new nodes in the appendable DB so each change traverses the
# trie updated by the prior ones. The probe applies a 3-change update list
# (a branch trie's three children) and outputs the final 32-byte root, which
# we diff against mpt_ref.py's `state_root` vector.
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

echo "==> emit zisk_mpt_state_root probe ELF"
lake exe codegen --program zisk_mpt_state_root --halt linux93 \
  -o "$REPO_ROOT/gen-out/zisk_mpt_state_root"

out="$VDIR/state_root.output"
"$ZISKEMU" -e "$REPO_ROOT/gen-out/zisk_mpt_state_root.elf" -i "$VDIR/state_root.input" \
  -o "$out" -n 8000000 >/dev/null 2>&1 </dev/null || { echo "  ERROR (ziskemu)"; exit 1; }
actual="$(xxd -p -l 32 "$out" | tr -d '\n')"
expected="$(cat "$VDIR/state_root.expected")"
if [[ "$actual" == "$expected" ]]; then
  echo "  PASS   state_root (3 sequential changes)  $actual"
  echo "==> PASS: mpt_state_root matches reference"
else
  echo "  FAIL   state_root"
  echo "    expected: $expected"
  echo "    actual:   $actual"
  echo "==> FAIL"; exit 1
fi
