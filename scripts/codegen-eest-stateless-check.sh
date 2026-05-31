#!/usr/bin/env bash
# codegen-eest-stateless-check.sh -- Run the RISC-V stateless guest against
# the EEST "zkevm" conformance fixtures and report a pass/fail baseline.
#
# Pipeline (end to end):
#   1. build the `stateless_guest` ELF via codegen -> as -> ld;
#   2. convert EEST zkevm fixtures (Amsterdam / Glamsterdam) into ziskemu
#      `-i` inputs + a manifest via scripts/eest-stateless-to-input.py;
#   3. run each guest input on ziskemu and compare its output against the
#      fixture's recorded `statelessOutputBytes`.
#
# Fixtures come from the release tarball fetched by
# scripts/eest-fetch-fixtures.sh (NOT re-filled locally); the EEST repo is
# vendored as the `execution-spec-tests` submodule for provenance.
#
# Conformance metrics reported per run:
#   * full   -- guest output == the full 105-byte expected result
#               (root + validation bit + chain_config).  Structurally
#               requires a *complete* guest; expect ~0 while the guest is
#               partial (its encoder emits the empty-active_fork variant
#               and computes a placeholder root / validation bit).
#   * succ   -- guest output byte[32] == expected byte[32], i.e. the
#               `successful_validation` decision matches.  This is the
#               primary near-term signal; byte 32 is the validation bit in
#               both layouts (a 32-byte root always precedes it).
#   * ERROR  -- ziskemu nonzero exit / step-budget exhaustion / truncated
#               output (e.g. the guest hit an Unimplemented exit).
#
# Usage:
#   scripts/codegen-eest-stateless-check.sh [options]
#     --all              run every stateless block (slow); default: smoke subset
#     --limit N          cap to N guest invocations (default 50)
#     --filter SUBSTR    only fixtures whose relpath contains SUBSTR
#     --steps N          ziskemu max steps (default $EEST_STEPS or 5000000)
#     --min-succ N       exit 1 if fewer than N succ-bit matches (regression gate)
#     --tag TAG          EEST fixture tag (default $EEST_FIXTURE_TAG or zkevm@v0.4.0)
#
# Exit:
#   0 -- ran to completion (baseline mode), or succ >= --min-succ
#   1 -- build/convert failure, no fixtures, or succ < --min-succ
set -euo pipefail

cd "$(dirname "$0")/.."
REPO_ROOT="$(pwd)"

ALL=0
LIMIT=50
FILTER=""
STEPS="${EEST_STEPS:-5000000}"
MIN_SUCC=""
TAG="${EEST_FIXTURE_TAG:-zkevm@v0.4.0}"

while [[ $# -gt 0 ]]; do
  case "$1" in
    --all) ALL=1; shift ;;
    --limit) LIMIT="$2"; shift 2 ;;
    --filter) FILTER="$2"; shift 2 ;;
    --steps) STEPS="$2"; shift 2 ;;
    --min-succ) MIN_SUCC="$2"; shift 2 ;;
    --tag) TAG="$2"; shift 2 ;;
    *) echo "unknown arg: $1" >&2; exit 1 ;;
  esac
done

# --- locate ziskemu ---------------------------------------------------------
ZISKEMU="${ZISKEMU:-}"
if [[ -z "$ZISKEMU" ]]; then
  if command -v ziskemu >/dev/null 2>&1; then
    ZISKEMU="$(command -v ziskemu)"
  elif [[ -x "$HOME/.zisk/bin/ziskemu" ]]; then
    ZISKEMU="$HOME/.zisk/bin/ziskemu"
  else
    echo "ziskemu not found -- install via ziskup or set ZISKEMU=..." >&2
    exit 1
  fi
fi

# --- locate fixtures --------------------------------------------------------
FX="${EEST_FIXTURES_DIR:-$REPO_ROOT/gen-out/eest-fixtures/$TAG/fixtures/fixtures}"
if [[ ! -d "$FX" ]]; then
  echo "EEST fixtures not found at: $FX" >&2
  echo "  run: scripts/eest-fetch-fixtures.sh '$TAG'" >&2
  exit 1
fi

mkdir -p gen-out

echo "==> lake build codegen"
lake build codegen

echo "==> emit stateless_guest ELF"
lake exe codegen --program stateless_guest --halt linux93 -o gen-out/stateless_guest

# --- convert fixtures -> ziskemu inputs + manifest --------------------------
RUN_DIR="$REPO_ROOT/gen-out/eest-run"
rm -rf "$RUN_DIR"
mkdir -p "$RUN_DIR"
conv_args=(--fixtures-dir "$FX" --out-dir "$RUN_DIR")
[[ "$ALL" -eq 0 ]] && conv_args+=(--limit "$LIMIT")
[[ -n "$FILTER" ]] && conv_args+=(--filter "$FILTER")
echo "==> convert fixtures (tag=$TAG, $([[ $ALL -eq 1 ]] && echo all || echo "limit=$LIMIT")${FILTER:+, filter=$FILTER})"
python3 scripts/eest-stateless-to-input.py "${conv_args[@]}"

MANIFEST="$RUN_DIR/manifest.tsv"
[[ -s "$MANIFEST" ]] || { echo "no stateless blocks selected" >&2; exit 1; }

# --- run + classify ---------------------------------------------------------
total=0 err=0 full=0 succ=0 fail=0
while IFS=$'\t' read -r label input expected_hex succ_bit input_len relpath; do
  total=$((total + 1))
  out="$RUN_DIR/$label.output"
  log="$RUN_DIR/$label.emu.log"
  if ! "$ZISKEMU" -e gen-out/stateless_guest.elf -i "$input" -o "$out" \
        -n "$STEPS" >"$log" 2>&1 </dev/null; then
    err=$((err + 1)); echo "  ERROR(exit)   $relpath"; continue
  fi
  actual_hex="$(xxd -p -l 105 "$out" 2>/dev/null | tr -d '\n' || true)"
  if [[ "${#actual_hex}" -lt 66 ]]; then
    err=$((err + 1)); echo "  ERROR(short)  $relpath"; continue
  fi
  exp="${expected_hex:0:210}"
  if [[ "$actual_hex" == "$exp" ]]; then
    full=$((full + 1)); succ=$((succ + 1)); echo "  PASS(full)    $relpath"; continue
  fi
  a_succ="${actual_hex:64:2}"; e_succ="${expected_hex:64:2}"
  if [[ "$a_succ" == "$e_succ" ]]; then
    succ=$((succ + 1)); echo "  pass(succ)    $relpath"
  else
    fail=$((fail + 1)); echo "  FAIL          $relpath (succ guest=$a_succ exp=$e_succ)"
  fi
done < "$MANIFEST"

ran=$((total - err))
# --- summary + baseline file ------------------------------------------------
BASELINE="$REPO_ROOT/gen-out/eest-baseline.txt"
{
  echo "EEST stateless-guest baseline"
  echo "  generated:   $(date -u '+%Y-%m-%dT%H:%M:%SZ')"
  echo "  fixture tag: $TAG"
  echo "  selection:   $([[ $ALL -eq 1 ]] && echo all || echo "limit=$LIMIT")${FILTER:+ filter=$FILTER}"
  echo "  ziskemu:     $ZISKEMU (steps=$STEPS)"
  echo "  total:       $total"
  echo "  errored:     $err"
  echo "  ran:         $ran"
  echo "  full match:  $full"
  echo "  succ match:  $succ"
  echo "  fail:        $fail"
} | tee "$BASELINE"

echo "==> wrote baseline: $BASELINE"

if [[ -n "$MIN_SUCC" && "$succ" -lt "$MIN_SUCC" ]]; then
  echo "==> REGRESSION: succ match $succ < --min-succ $MIN_SUCC" >&2
  exit 1
fi
exit 0
