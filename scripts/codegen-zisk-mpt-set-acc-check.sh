#!/usr/bin/env bash
# codegen-zisk-mpt-set-acc-check.sh -- verify the ACCUMULATING MPT update
# (bead evm-asm-fhsxz.4.3.1) against the validated Python reference.
#
# mpt_set_acc threads an appendable node DB so sequential updates compose:
# after update 1 the root node changes, so update 2 must resolve the new root
# from the DB (and an unchanged sibling leaf from the witness). The probe
# applies TWO value-only updates and outputs the final 32-byte root; we diff
# it against mpt_ref.py's `acc` vector (two leaves under a branch, updated at
# nibbles 1 then 2).
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

echo "==> emit zisk_mpt_set_acc probe ELF"
lake exe codegen --program zisk_mpt_set_acc --halt linux93 \
  -o "$REPO_ROOT/gen-out/zisk_mpt_set_acc"

out="$VDIR/acc.output"
"$ZISKEMU" -e "$REPO_ROOT/gen-out/zisk_mpt_set_acc.elf" -i "$VDIR/acc.input" \
  -o "$out" -n 5000000 >/dev/null 2>&1 </dev/null || { echo "  ERROR (ziskemu)"; exit 1; }
actual="$(xxd -p -l 32 "$out" | tr -d '\n')"
expected="$(cat "$VDIR/acc.expected")"
if [[ "$actual" == "$expected" ]]; then
  echo "  PASS   acc (2 sequential updates)  $actual"
  echo "==> PASS: mpt_set_acc matches reference"
else
  echo "  FAIL   acc"
  echo "    expected: $expected"
  echo "    actual:   $actual"
  echo "==> FAIL"; exit 1
fi
