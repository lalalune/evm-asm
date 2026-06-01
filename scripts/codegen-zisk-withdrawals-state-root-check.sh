#!/usr/bin/env bash
# codegen-zisk-withdrawals-state-root-check.sh -- verify withdrawals_state_root
# (bead evm-asm-fhsxz.2.2): the computational heart of the Step-2 verdict.
#
# Given a pre-state trie (two accounts) + the block's withdrawals, recompute
# the post-state MPT root by crediting each recipient's balance. Composes
# withdrawal_to_path_delta + mpt_walk + account_add_balance + mpt_state_root.
# The probe outputs the post-state root (OUTPUT+0); we diff it against
# mpt_ref.py's withdrawal vector (2 accounts, 2 withdrawals).
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

echo "==> emit zisk_withdrawals_state_root probe ELF"
lake exe codegen --program zisk_withdrawals_state_root --halt linux93 \
  -o "$REPO_ROOT/gen-out/zisk_withdrawals_state_root"

out="$VDIR/wsr.output"
"$ZISKEMU" -e "$REPO_ROOT/gen-out/zisk_withdrawals_state_root.elf" -i "$VDIR/wsr.input" \
  -o "$out" -n 12000000 >/dev/null 2>&1 </dev/null || { echo "  ERROR (ziskemu)"; exit 1; }
actual="$(xxd -p -l 32 "$out" | tr -d '\n')"
status="$(od -An -tu8 -j 32 -N 8 "$out" | tr -d ' \n')"
expected="$(cat "$VDIR/wsr.expected")"
if [[ "$actual" == "$expected" ]]; then
  echo "  PASS   wsr (2 accounts, 2 withdrawals)  status=$status  $actual"
  echo "==> PASS: withdrawals_state_root matches reference"
else
  echo "  FAIL   wsr  status=$status"
  echo "    expected: $expected"
  echo "    actual:   $actual"
  echo "==> FAIL"; exit 1
fi
