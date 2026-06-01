#!/usr/bin/env bash
# codegen-zisk-account-add-balance-check.sh -- verify account_add_balance
# (bead evm-asm-fhsxz.2.1) against the Python account-RLP reference.
#
# account_add_balance credits a wei delta to the balance field of an account
# RLP (rlp([nonce, balance, storageRoot, codeHash])) — the per-withdrawal
# state mutation Step 2 applies before recomputing the post-state root. The
# probe outputs the new account RLP (len at OUTPUT+0, bytes at OUTPUT+8); we
# diff it against mpt_ref.py's account_encode for several (balance, delta)
# cases (byte growth, 0-start, 8-byte carry boundary, +0 no-op).
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

echo "==> emit zisk_account_add_balance probe ELF"
lake exe codegen --program zisk_account_add_balance --halt linux93 \
  -o "$REPO_ROOT/gen-out/zisk_account_add_balance"

fail=0
for name in aab1 aab2 aab3 aab4; do
  out="$VDIR/$name.output"
  "$ZISKEMU" -e "$REPO_ROOT/gen-out/zisk_account_add_balance.elf" \
    -i "$VDIR/$name.input" -o "$out" -n 2000000 >/dev/null 2>&1 </dev/null \
    || { echo "  ERROR  $name"; fail=1; continue; }
  len="$(od -An -tu8 -j 0 -N 8 "$out" | tr -d ' \n')"
  actual="$(xxd -p -s 8 -l "$len" "$out" | tr -d '\n')"
  expected="$(cat "$VDIR/$name.expected")"
  if [[ "$actual" == "$expected" ]]; then echo "  PASS   $name  $actual"
  else echo "  FAIL   $name"; echo "    expected: $expected"; echo "    actual:   $actual"; fail=1; fi
done
[[ "$fail" -eq 0 ]] && echo "==> PASS: account_add_balance matches reference" \
  || { echo "==> FAIL"; exit 1; }
