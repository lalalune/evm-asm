#!/usr/bin/env bash
# codegen-smoke.sh — M0 smoke driver.
#
# Builds the codegen tool, emits the synthetic ADD program for both halt
# conventions, and (if the cross toolchain is present) assembles & links
# both into ELFs under gen-out/. Run from the repo root.
#
# Usage:
#   scripts/codegen-smoke.sh [--asm-only]
#
# Exit codes:
#   0 — emission succeeded (and assembly/link succeeded if attempted)
#   1 — emission or assembly/link failed
set -euo pipefail

cd "$(dirname "$0")/.."

ASM_ONLY=""
if [[ "${1:-}" == "--asm-only" ]]; then
  ASM_ONLY="--asm-only"
fi

mkdir -p gen-out

echo "==> lake build codegen"
lake build codegen

for halt in linux93 sp1; do
  echo "==> lake exe codegen --program smoke --halt ${halt} -o gen-out/smoke-${halt} ${ASM_ONLY}"
  lake exe codegen --program smoke --halt "${halt}" -o "gen-out/smoke-${halt}" ${ASM_ONLY}
done

echo
echo "==> emitted files:"
ls -l gen-out/
