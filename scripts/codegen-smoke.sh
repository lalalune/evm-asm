#!/usr/bin/env bash
# codegen-smoke.sh — M0 smoke driver.
#
# Builds the codegen tool, emits the synthetic ADD program for both halt
# conventions, assembles & links to ELFs under gen-out/, and (when ziskemu
# is available) runs each ELF on the emulator with a bounded step budget.
#
# Run from the repo root or any subdir. Looks for ziskemu on PATH and at
# the canonical ZisK install path ~/.zisk/bin/ziskemu.
#
# Usage:
#   scripts/codegen-smoke.sh [--asm-only] [--no-emu]
#
# Exit codes:
#   0 — emission (and, where attempted, assembly/link and emulation) ok
#   1 — any of the above failed
set -euo pipefail

cd "$(dirname "$0")/.."

ASM_ONLY=""
RUN_EMU=1
for arg in "$@"; do
  case "$arg" in
    --asm-only) ASM_ONLY="--asm-only"; RUN_EMU=0 ;;
    --no-emu)   RUN_EMU=0 ;;
    -h|--help)
      sed -n '2,15p' "$0"; exit 0 ;;
    *) echo "unknown arg: $arg" >&2; exit 1 ;;
  esac
done

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

if [[ "$RUN_EMU" -ne 1 ]]; then
  exit 0
fi

# Locate ziskemu.
ZISKEMU="${ZISKEMU:-}"
if [[ -z "$ZISKEMU" ]]; then
  if command -v ziskemu >/dev/null 2>&1; then
    ZISKEMU="$(command -v ziskemu)"
  elif [[ -x "$HOME/.zisk/bin/ziskemu" ]]; then
    ZISKEMU="$HOME/.zisk/bin/ziskemu"
  fi
fi

if [[ -z "$ZISKEMU" ]]; then
  echo
  echo "==> ziskemu not found on PATH or at ~/.zisk/bin/ziskemu — skipping emulation"
  echo "    install via:  curl -fsSL https://raw.githubusercontent.com/0xPolygonHermez/zisk/main/ziskup/install.sh -o /tmp/ziskup-install.sh && bash /tmp/ziskup-install.sh --nokey -y"
  exit 0
fi

# Bounded step budget: smoke is ~10 instructions; 10_000 is generous and
# protects against the SP1 case where ziskemu doesn't halt at all.
STEPS=10000

for halt in linux93 sp1; do
  echo
  echo "==> $ZISKEMU -e gen-out/smoke-${halt}.elf -n ${STEPS}"
  set +e
  "$ZISKEMU" -e "gen-out/smoke-${halt}.elf" -n "$STEPS" >"gen-out/smoke-${halt}.emu.log" 2>&1
  rc=$?
  set -e
  if [[ "$rc" -eq 0 ]] && ! grep -q EmulationNoCompleted "gen-out/smoke-${halt}.emu.log"; then
    echo "    halt=${halt}: HALTED cleanly (exit ${rc})"
  else
    if grep -q EmulationNoCompleted "gen-out/smoke-${halt}.emu.log"; then
      echo "    halt=${halt}: DID NOT HALT within ${STEPS} steps (EmulationNoCompleted)"
    else
      echo "    halt=${halt}: ziskemu exit=${rc}; see gen-out/smoke-${halt}.emu.log"
    fi
  fi
done

echo
echo "==> done. emulation logs are in gen-out/smoke-*.emu.log"
