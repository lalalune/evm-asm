#!/usr/bin/env bash
# codegen-zisk-bal-account-path-check.sh -- verify bal_account_path
# against the Python BAL AccountChanges reference.
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

echo "==> emit zisk_bal_account_path probe ELF"
lake exe codegen --program zisk_bal_account_path --halt linux93 \
  -o "$REPO_ROOT/gen-out/zisk_bal_account_path"

fail=0
for name in bacp_empty bacp_changes bacp_precompile; do
  out="$VDIR/$name.output"
  "$ZISKEMU" -e "$REPO_ROOT/gen-out/zisk_bal_account_path.elf" \
    -i "$VDIR/$name.input" -o "$out" -n 2000000 >/dev/null 2>&1 </dev/null \
    || { echo "  ERROR  $name"; fail=1; continue; }
  status="$(od -An -tu8 -j 0 -N 8 "$out" | tr -d ' \n')"
  actual="$(xxd -p -s 8 -l 64 "$out" | tr -d '\n')"
  expected="$(cat "$VDIR/$name.path")"
  if [[ "$status" == "0" && "$actual" == "$expected" ]]; then echo "  PASS   $name  ${actual:0:32}..."
  else echo "  FAIL   $name status=$status"; echo "    expected: $expected"; echo "    actual:   $actual"; fail=1; fi
done
[[ "$fail" -eq 0 ]] && echo "==> PASS: bal_account_path matches reference" \
  || { echo "==> FAIL"; exit 1; }
