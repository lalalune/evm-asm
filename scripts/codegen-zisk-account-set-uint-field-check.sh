#!/usr/bin/env bash
# codegen-zisk-account-set-uint-field-check.sh -- verify account_set_uint_field
# against the Python account-RLP reference.
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

echo "==> emit zisk_account_set_uint_field probe ELF"
lake exe codegen --program zisk_account_set_uint_field --halt linux93 \
  -o "$REPO_ROOT/gen-out/zisk_account_set_uint_field"

fail=0
for name in asuf_nonce asuf_balance asuf_zero_balance; do
  out="$VDIR/$name.output"
  "$ZISKEMU" -e "$REPO_ROOT/gen-out/zisk_account_set_uint_field.elf" \
    -i "$VDIR/$name.input" -o "$out" -n 2000000 >/dev/null 2>&1 </dev/null \
    || { echo "  ERROR  $name"; fail=1; continue; }
  len="$(od -An -tu8 -j 0 -N 8 "$out" | tr -d ' \n')"
  actual="$(xxd -p -s 8 -l "$len" "$out" | tr -d '\n')"
  expected="$(cat "$VDIR/$name.expected")"
  if [[ "$actual" == "$expected" ]]; then echo "  PASS   $name  $actual"
  else echo "  FAIL   $name"; echo "    expected: $expected"; echo "    actual:   $actual"; fail=1; fi
done
[[ "$fail" -eq 0 ]] && echo "==> PASS: account_set_uint_field matches reference" \
  || { echo "==> FAIL"; exit 1; }
