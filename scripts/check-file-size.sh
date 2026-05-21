#!/usr/bin/env bash
#
# check-file-size.sh — enforce the per-file line caps described in
# AGENTS.md ("File-size guardrail") and tracked by issue #314.
#
# Caps (lines, inclusive):
#   * EvmAsm/Evm64/**/Compose/**/*.lean       hard cap 1200 (soft cap 1000)
#   * EvmAsm/Evm64/**/*.lean (everything else) hard cap 1500
#
# Structural exemption:
#   * Files named Program.lean are exempt — concrete bytecode + tests
#     are intrinsically long and cheap to compile.
#
# Usage:
#   scripts/check-file-size.sh           # exit 1 on any violation
#   scripts/check-file-size.sh --report  # always exit 0; print summary
#
# The script intentionally stays POSIX/bash with no external deps so it
# runs in CI and as a pre-commit hook without setup.

set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
ROOT_REL="EvmAsm/Evm64"
COMPOSE_CAP=1200
DEFAULT_CAP=1500

mode="enforce"
if [[ ${1:-} == "--report" ]]; then
  mode="report"
fi

violations=0
checked=0

# Collect files in deterministic order.
mapfile -t files < <(cd "$ROOT" && find "$ROOT_REL" -name '*.lean' -type f | LC_ALL=C sort)

for rel in "${files[@]}"; do
  path="$ROOT/$rel"
  base="${rel##*/}"

  # Program.lean files are intrinsically bytecode-shaped; skip.
  if [[ "$base" == "Program.lean" ]]; then
    continue
  fi

  checked=$((checked + 1))

  if [[ "$rel" == */Compose/* ]]; then
    cap=$COMPOSE_CAP
    bucket="Compose"
  else
    cap=$DEFAULT_CAP
    bucket="opcode"
  fi

  lines=$(wc -l < "$path")

  if (( lines <= cap )); then
    continue
  fi

  violations=$((violations + 1))
  printf '  FAIL    %4d / %d lines  %s  [%s]\n' \
    "$lines" "$cap" "$rel" "$bucket"
done

if [[ "$mode" == "report" ]]; then
  printf '\nchecked %d files, %d over cap\n' "$checked" "$violations"
  exit 0
fi

if (( violations > 0 )); then
  cat >&2 <<EOF

==================================================================
File-size guardrail failed: $violations file(s) exceed the cap.

Caps:
  Compose/**/*.lean   $COMPOSE_CAP lines
  other Lean files    $DEFAULT_CAP lines  (Program.lean exempt)

To fix, split the file. Compose/ is the canonical pattern — see
AGENTS.md "Parallel file splitting for Compose files". The DivMod
Compose split took monolithic build time from 87s to 55s.
==================================================================
EOF
  exit 1
fi

printf 'file-size guardrail: %d files checked, all within cap.\n' "$checked"
