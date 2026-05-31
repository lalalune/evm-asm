#!/usr/bin/env bash
# codegen-zisk-mpt-set-check.sh -- verify the MPT post-state-root recompute
# (mpt_set, value-only update of an existing key) against the validated
# Python reference scripts/mpt_ref.py.
#
# This is the verification harness for the EEST full-match BLOCKER
# (bead evm-asm-fhsxz.4): recomputing the post-state MPT root after a
# state change, so the guest can soundly set successful_validation.
#
# Pipeline: mpt_ref.py builds (witness, root, path, new_value, expected
# new_root) vectors for three trie shapes (leaf / branch / extension+branch)
# and a ziskemu `-i` probe input each; the zisk_mpt_set probe recomputes the
# root; we diff the 32-byte output against the reference.
#
# mpt_ref.py is VALIDATED: its leaf-shape root matches the guest's existing
# `zisk_single_leaf_trie_root` byte-for-byte (same RLP/HP/keccak).
#
# STATUS: the zisk_mpt_set probe (the record-walk + bubble-up asm) is the
# work item; until it is registered in EvmAsm/Codegen/Programs.lean this
# script generates + reports the vectors and skips the run.
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

if ! lake exe codegen --program zisk_mpt_set --halt linux93 -o "$REPO_ROOT/gen-out/zisk_mpt_set" 2>/dev/null; then
  echo "==> zisk_mpt_set probe not yet implemented; vectors ready in $VDIR" >&2
  echo "    (implement mpt_set per bead evm-asm-fhsxz.4, then re-run this script)" >&2
  exit 0
fi

fail=0
for name in leaf branch ext_branch; do
  out="$REPO_ROOT/gen-out/mpt-set/$name.output"
  "$ZISKEMU" -e "$REPO_ROOT/gen-out/zisk_mpt_set.elf" -i "$VDIR/$name.input" \
    -o "$out" -n 5000000 >/dev/null 2>&1 </dev/null || { echo "  ERROR  $name"; fail=1; continue; }
  actual="$(xxd -p -l 32 "$out" | tr -d '\n')"
  expected="$(cat "$VDIR/$name.expected")"
  if [[ "$actual" == "$expected" ]]; then echo "  PASS   $name  $actual"
  else echo "  FAIL   $name"; echo "    expected: $expected"; echo "    actual:   $actual"; fail=1; fi
done
[[ "$fail" -eq 0 ]] && echo "==> PASS: mpt_set recompute matches reference" || { echo "==> FAIL"; exit 1; }
