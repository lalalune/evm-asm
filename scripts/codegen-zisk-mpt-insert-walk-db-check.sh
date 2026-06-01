#!/usr/bin/env bash
# codegen-zisk-mpt-insert-walk-db-check.sh -- verify mpt_insert_walk_db (bead
# evm-asm-fhsxz.2.4.2.6.5): the DB-aware divergence walk must classify the same
# way as the witness-only mpt_insert_walk. With an EMPTY node DB every node is
# resolved from the witness, so the DB/layout-INDEPENDENT meta fields (depth,
# consumed, case, match_len) must equal the mpt_insert_walk expectations from
# scripts/mpt_ref.py. (The absolute node-ptr fields are layout-dependent and
# are validated end-to-end by mpt_insert_acc.)
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

echo "==> emit zisk_mpt_insert_walk_db probe ELF"
lake exe codegen --program zisk_mpt_insert_walk_db --halt linux93 \
  -o "$REPO_ROOT/gen-out/zisk_mpt_insert_walk_db"

read_u64() { od -An -tu8 -j "$2" -N 8 "$1" | tr -d ' \n'; }

fail=0
for name in iw_branch_empty iw_leaf_split iw_ext_split iw_empty_trie \
            iw_ext_then_branch_empty; do
  out="$VDIR/$name.iwdb.output"
  if ! "$ZISKEMU" -e "$REPO_ROOT/gen-out/zisk_mpt_insert_walk_db.elf" \
        -i "$VDIR/$name.input" -o "$out" -n 5000000 >/dev/null 2>&1 </dev/null; then
    echo "  ERROR  $name (ziskemu)"; fail=1; continue
  fi
  shape_ok=1; details=""
  while read -r field off exp; do
    [[ -z "$field" ]] && continue
    # only the DB/layout-independent classification fields
    case "$field" in depth|consumed|case|match_len) ;; *) continue ;; esac
    act="$(read_u64 "$out" "$off")"
    if [[ "$act" != "$exp" ]]; then
      shape_ok=0; details+=$'\n'"      $field @${off}: expected $exp got $act"
    fi
  done < "$VDIR/$name.iwexpected"
  st="$(read_u64 "$out" 0)"
  [[ "$st" != "0" ]] && { shape_ok=0; details+=$'\n'"      status=$st"; }
  if [[ "$shape_ok" -eq 1 ]]; then
    c="$(read_u64 "$out" 24)"; echo "  PASS   $name  (case=$c)"
  else
    echo "  FAIL   $name$details"; fail=1
  fi
done
[[ "$fail" -eq 0 ]] && echo "==> PASS: mpt_insert_walk_db classification matches reference" \
  || { echo "==> FAIL"; exit 1; }
