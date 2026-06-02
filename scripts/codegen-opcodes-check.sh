#!/usr/bin/env bash
# codegen-opcodes-check.sh — generic per-opcode regression runner.
#
# Enumerates Lean-declared test cases (`EvmAsm/Codegen/Tests/Cases.lean`)
# via `lake exe codegen --list-test-cases`, then for each case:
#   1. emits an ELF via `lake exe codegen --test-case <name>` (wraps the
#      bytecode through the M5b dispatcher's `tinyInterpRegistry`)
#   2. runs it on ziskemu
#   3. diffs the first 32 bytes of ziskemu's `-o` output against the
#      case's `expectedOutHex`.
#
# Adding a new opcode regression = appending one record to
# `opcodeTestCases` in `Tests/Cases.lean` — no edits to this script.
#
# Exit:
#   0 — all cases match expected
#   1 — emission / build / emulation failed, or any output mismatch
set -euo pipefail

cd "$(dirname "$0")/.."

ZISKEMU="${ZISKEMU:-}"
if [[ -z "$ZISKEMU" ]]; then
  if command -v ziskemu >/dev/null 2>&1; then
    ZISKEMU="$(command -v ziskemu)"
  elif [[ -x "$HOME/.zisk/bin/ziskemu" ]]; then
    ZISKEMU="$HOME/.zisk/bin/ziskemu"
  else
    echo "ziskemu not found — install via ziskup or set ZISKEMU=..." >&2
    exit 1
  fi
fi

mkdir -p gen-out

echo "==> lake build codegen"
lake build codegen

# `lake exe codegen --list-test-cases` emits `<name>\t<expectedOutHex>`
# per line; we read both columns. Single source of truth lives in
# `EvmAsm/Codegen/Tests/Cases.lean`. Uses portable `while read` so the
# script works on the macOS bash 3.2 default (no `mapfile`).

LIST_FILE="gen-out/.opcodes-list"
lake exe codegen --list-test-cases >"$LIST_FILE"

TOTAL=0
while IFS= read -r _; do TOTAL=$((TOTAL + 1)); done <"$LIST_FILE"

if [[ "$TOTAL" -eq 0 ]]; then
  echo "==> no test cases declared in opcodeTestCases" >&2
  exit 1
fi

echo "==> running $TOTAL test case(s)"

FAILED=()
SKIPPED=0
# `--list-test-cases` emits TSV with optional runtime-input columns.
# This legacy runner bakes bytecode into `.data` and has no input
# trailer, so it skips cases that require calldata, storage preload, or
# nonzero blob-base-fee input.
while IFS= read -r line; do
  name=$(printf '%s' "$line" | cut -f1)
  expected=$(printf '%s' "$line" | cut -f2)
  calldata=$(printf '%s' "$line" | cut -f4)
  storage=$(printf '%s' "$line" | cut -f5)
  blob_base_fee=$(printf '%s' "$line" | cut -f6)
  if [[ -z "$name" || -z "$expected" ]]; then
    echo
    echo "==> SKIP: malformed --list-test-cases line"
    FAILED+=("${name:-<unknown>} (malformed-tsv)")
    continue
  fi

  if [[ -n "${calldata:-}" || -n "${storage:-}" || -n "${blob_base_fee:-}" ]]; then
    echo
    echo "==> SKIP: $name requires runtime input trailer"
    SKIPPED=$((SKIPPED + 1))
    continue
  fi

  echo
  echo "==> emit $name"
  lake exe codegen --test-case "$name" --halt linux93 -o "gen-out/$name"

  echo "==> ziskemu -e gen-out/$name.elf -o gen-out/$name.output"
  "$ZISKEMU" -e "gen-out/$name.elf" -o "gen-out/$name.output" -n 500000 \
    >"gen-out/$name.emu.log" 2>&1

  actual="$(xxd -p -c 64 -l 32 "gen-out/$name.output" | tr -d '\n')"

  echo "expected:"
  echo "  $expected"
  echo "actual:"
  echo "  $actual"

  if [[ "$actual" == "$expected" ]]; then
    echo "==> PASS: $name"
  else
    echo "==> FAIL: $name output mismatch"
    FAILED+=("$name")
  fi
done <"$LIST_FILE"

echo
if [[ ${#FAILED[@]} -eq 0 ]]; then
  if [[ "$SKIPPED" -eq 0 ]]; then
    echo "==> ALL PASS ($TOTAL case(s))"
  else
    echo "==> ALL PASS ($((TOTAL - SKIPPED)) run, $SKIPPED skipped runtime-input case(s))"
  fi
  exit 0
else
  echo "==> FAIL: ${#FAILED[@]} of $TOTAL case(s) failed:"
  for f in "${FAILED[@]}"; do
    echo "    - $f"
  done
  exit 1
fi
