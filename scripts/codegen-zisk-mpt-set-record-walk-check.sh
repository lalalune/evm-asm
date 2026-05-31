#!/usr/bin/env bash
# codegen-zisk-mpt-set-record-walk-check.sh -- verify the MPT post-state-root
# recompute RECORD-WALK (bead evm-asm-fhsxz.4.2.1) against the validated
# Python reference scripts/mpt_ref.py.
#
# The record-walk forks mpt_walk: it descends the trie exactly the same way
# but, instead of extracting the value, emits the descent node-stack
# (root..leaf) that the bubble-up pass (.4.2.2) will re-encode. This harness
# runs the `zisk_mpt_set_record_walk` probe on three trie shapes (leaf depth 0
# / branch depth 1 / extension+branch depth 2) and checks every u64 field of
# the probe OUTPUT against mpt_ref's prediction.
#
# Probe OUTPUT layout (u64 fields, little-endian):
#   +0   status (0 found / 1 not-found / 2 parse-fail)
#   +8   meta.depth        +16 meta.consumed
#   +24  meta.leaf_offset  +32 meta.leaf_len
#   +128 record[i] = (node_offset, node_len, kind, nibble), 32 B each
#
# mpt_ref.py emits "<field> <output_byte_offset> <u64_value>" lines per shape
# in <name>.rwexpected; we read each u64 from OUTPUT (od -tu8) and diff.
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

echo "==> emit zisk_mpt_set_record_walk probe ELF"
lake exe codegen --program zisk_mpt_set_record_walk --halt linux93 \
  -o "$REPO_ROOT/gen-out/zisk_mpt_set_record_walk"

read_u64() {  # read_u64 <file> <byte_offset>  -> decimal u64 (little-endian)
  od -An -tu8 -j "$2" -N 8 "$1" | tr -d ' \n'
}

fail=0
for name in leaf branch ext_branch; do
  out="$VDIR/$name.rw.output"
  if ! "$ZISKEMU" -e "$REPO_ROOT/gen-out/zisk_mpt_set_record_walk.elf" \
        -i "$VDIR/$name.input" -o "$out" -n 5000000 >/dev/null 2>&1 </dev/null; then
    echo "  ERROR  $name (ziskemu)"; fail=1; continue
  fi
  shape_ok=1; details=""
  while read -r field off exp; do
    [[ -z "$field" ]] && continue
    act="$(read_u64 "$out" "$off")"
    if [[ "$act" != "$exp" ]]; then
      shape_ok=0; details+=$'\n'"      $field @${off}: expected $exp got $act"
    fi
  done < "$VDIR/$name.rwexpected"
  if [[ "$shape_ok" -eq 1 ]]; then
    d="$(read_u64 "$out" 8)"
    echo "  PASS   $name  (depth=$d)"
  else
    echo "  FAIL   $name$details"; fail=1
  fi
done
[[ "$fail" -eq 0 ]] && echo "==> PASS: mpt_set record-walk matches reference" \
  || { echo "==> FAIL"; exit 1; }
