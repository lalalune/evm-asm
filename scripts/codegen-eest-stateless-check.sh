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
# Conformance metrics reported per run -- the 105-byte
# SszStatelessValidationResult decomposes into three independently
# checkable regions, each reported separately so we can see *where* the
# guest is right, not just full-vs-not:
#   * root   -- bytes 0:32  == expected: new_payload_request_root
#               (computed by the epilogue's SSZ merkle tree; currently
#               mismatches when the block has non-empty transactions /
#               withdrawals / requests / block_access_list, since those
#               list field-roots are still static constants).
#   * succ   -- byte 32     == expected: successful_validation bit.
#   * tail   -- bytes 33:105 == expected: u32 offset (=37) + the 68-byte
#               chain_config (echoed from the input by the encoder).
#   * full   -- all 105 bytes match (root AND succ AND tail).
#   * ERROR  -- ziskemu nonzero exit / step-budget exhaustion / truncated
#               output (e.g. the guest hit an Unimplemented exit).
# A per-FAIL line shows which regions matched, e.g. "[root/----/tail]".
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
# Default step cap. ziskemu stops at the guest's halt, so this only bounds
# runaway/very-large runs -- raised to 50M so many-deposit / large-tx blocks
# (whose NPR-root merkleization is sha256-heavy) complete; normal blocks
# halt long before this and are not slowed.
STEPS="${EEST_STEPS:-50000000}"
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
# The 105-byte SszStatelessValidationResult decomposes into three
# independently-checkable regions, so we report each separately to show
# exactly where the guest stands (not just full-vs-not):
#   root [0:32]   = new_payload_request_root  (hex chars 0..64)
#   succ [32]     = successful_validation     (hex chars 64..66)
#   tail [33:105] = u32 offset (=37) + 68-byte chain_config (hex 66..210)
total=0 err=0 full=0 succ=0 root=0 tail=0 fail=0 rod=0
while IFS=$'\t' read -r label input expected_hex succ_bit input_len relpath; do
  total=$((total + 1))
  out="$RUN_DIR/$label.output"
  log="$RUN_DIR/$label.emu.log"
  if ! "$ZISKEMU" -e gen-out/stateless_guest.elf -i "$input" -o "$out" \
        -n "$STEPS" >"$log" 2>&1 </dev/null; then
    err=$((err + 1)); echo "  ERROR(exit)   $relpath"; continue
  fi
  actual_hex="$(xxd -p -l 105 "$out" 2>/dev/null | tr -d '\n' || true)"
  if [[ "${#actual_hex}" -lt 210 ]]; then
    err=$((err + 1)); echo "  ERROR(short)  $relpath (${#actual_hex} hex chars)"; continue
  fi
  exp="${expected_hex:0:210}"

  # Per-region matches.
  [[ "${actual_hex:0:64}"   == "${exp:0:64}"   ]] && { root=$((root + 1)); r=root; } || r=----
  [[ "${actual_hex:64:2}"   == "${exp:64:2}"   ]] && { succ=$((succ + 1)); s=succ; } || s=----
  [[ "${actual_hex:66:144}" == "${exp:66:144}" ]] && { tail=$((tail + 1)); t=tail; } || t=----

  if [[ "$actual_hex" == "$exp" ]]; then
    full=$((full + 1)); echo "  PASS(full)        $relpath"
  else
    fail=$((fail + 1))
    # root-only diff: succ + tail already match, ONLY the 32-byte root
    # differs -- i.e. this block is exactly one field (the NPR root) from
    # a full match. This is the precise "distance to crown jewel" metric.
    [[ "$s" == "succ" && "$t" == "tail" && "$r" == "----" ]] && rod=$((rod + 1))
    echo "  FAIL [$r/$s/$t]  $relpath (succ guest=${actual_hex:64:2} exp=${exp:64:2})"
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
  echo "  full match:    $full   (all 105 bytes)"
  echo "  root match:    $root   (bytes 0:32  = new_payload_request_root)"
  echo "  succ match:    $succ   (byte 32     = successful_validation)"
  echo "  tail match:    $tail   (bytes 33:105 = offset + chain_config)"
  echo "  root-only diff:$rod   (succ+tail match; ONLY root differs => 1 field from full)"
  echo "  fail:          $fail"
} | tee "$BASELINE"

echo "==> wrote baseline: $BASELINE"

if [[ -n "$MIN_SUCC" && "$succ" -lt "$MIN_SUCC" ]]; then
  echo "==> REGRESSION: succ match $succ < --min-succ $MIN_SUCC" >&2
  exit 1
fi
exit 0
