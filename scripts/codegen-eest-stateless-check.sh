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
#     --steps N          ziskemu max steps (default $EEST_STEPS or 50000000)
#     --min-succ N       exit 1 if fewer than N succ-bit matches (regression gate)
#     --min-full N       exit 1 if fewer than N full (105-byte) matches (regression gate)
#     --min-root N       exit 1 if fewer than N root matches (regression gate)
#     --tag TAG          EEST fixture tag (default $EEST_FIXTURE_TAG or zkevm@v0.4.0)
#     --jobs N           run N ziskemu invocations in parallel (default: auto).
#                        The auto value is derived from the ziskemu build: a
#                        stock build peaks at ~6.5 GB RSS per process (because it
#                        allocates a flat ROM array spanning the 127 MB gap up to
#                        the embedded float library), so only a few fit in RAM; a
#                        "PATCHED-lowmem" build (float library split into its own
#                        array) peaks at ~22 MB, so we can run ~one-per-core.
#                        See ziskemu --version to tell which build is installed.
#                        Override with --jobs N or $EEST_JOBS.
#
# Exit:
#   0 -- ran to completion (baseline mode), or all --min-* thresholds met
#   1 -- build/convert failure, no fixtures, or a --min-{succ,full,root} regression
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
MIN_FULL=""
MIN_ROOT=""
TAG="${EEST_FIXTURE_TAG:-zkevm@v0.4.0}"
# Parallelism: empty => auto-detect from the ziskemu build (see below).
JOBS="${EEST_JOBS:-}"

while [[ $# -gt 0 ]]; do
  case "$1" in
    --all) ALL=1; shift ;;
    --limit) LIMIT="$2"; shift 2 ;;
    --filter) FILTER="$2"; shift 2 ;;
    --steps) STEPS="$2"; shift 2 ;;
    --min-succ) MIN_SUCC="$2"; shift 2 ;;
    --min-full) MIN_FULL="$2"; shift 2 ;;
    --min-root) MIN_ROOT="$2"; shift 2 ;;
    --tag) TAG="$2"; shift 2 ;;
    --jobs) JOBS="$2"; shift 2 ;;
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

# --- pick parallelism based on the ziskemu build ----------------------------
# ziskemu's peak RSS is dominated by a fixed allocation built at ELF-load time,
# independent of the program or step budget. A stock build keeps every ROM
# instruction in one flat array indexed from the program base; because the
# embedded float library is linked ~127 MB above the program, that array spans
# the whole gap (~33M entries) and costs ~6.5 GB. A "PATCHED-lowmem" build moves
# the float library into its own array, dropping peak RSS to ~22 MB. We size the
# job pool accordingly: stock => memory-bound (few jobs); patched => core-bound.
ZISKEMU_VERSION="$("$ZISKEMU" --version 2>/dev/null || echo unknown)"
if [[ "$ZISKEMU_VERSION" == *PATCHED-lowmem* ]]; then
  ZISKEMU_FLAVOR="patched-lowmem"
  PER_PROC_MB=128          # ~22 MB peak + headroom
else
  ZISKEMU_FLAVOR="stock"
  PER_PROC_MB=7000         # ~6.5 GB peak, rounded up
fi

CPUS="$(nproc 2>/dev/null || echo 1)"
if [[ -z "$JOBS" ]]; then
  # MemAvailable is the realistic cap; fall back to MemTotal, then 1 job.
  AVAIL_MB="$(awk '/^MemAvailable:/{print int($2/1024); f=1} END{if(!f) print 0}' /proc/meminfo 2>/dev/null || echo 0)"
  [[ "$AVAIL_MB" -le 0 ]] && AVAIL_MB="$(awk '/^MemTotal:/{print int($2/1024)}' /proc/meminfo 2>/dev/null || echo "$PER_PROC_MB")"
  MEM_JOBS=$(( AVAIL_MB / PER_PROC_MB ))
  (( MEM_JOBS < 1 )) && MEM_JOBS=1
  JOBS=$(( CPUS < MEM_JOBS ? CPUS : MEM_JOBS ))
fi
(( JOBS < 1 )) && JOBS=1

echo "==> ziskemu: $ZISKEMU"
echo "    version: $ZISKEMU_VERSION"
echo "    flavor:  $ZISKEMU_FLAVOR (~${PER_PROC_MB} MB/proc budget) -> jobs=$JOBS (cpus=$CPUS)"

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
# Phase 1 -- run every guest input on ziskemu, up to $JOBS at a time. Each run
# records its exit code to "$RUN_DIR/$label.exit"; classification (phase 2) is
# kept serial so the tallies and the per-fixture report stay deterministic and
# in manifest order regardless of $JOBS.
run_one() {
  local label="$1" input="$2"
  local rc=0
  "$ZISKEMU" -e gen-out/stateless_guest.elf -i "$input" -o "$RUN_DIR/$label.output" \
      -n "$STEPS" >"$RUN_DIR/$label.emu.log" 2>&1 </dev/null || rc=$?
  printf '%s' "$rc" > "$RUN_DIR/$label.exit"
}

echo "==> run $(wc -l < "$MANIFEST" | tr -d ' ') guest inputs on ziskemu (jobs=$JOBS)"
while IFS=$'\t' read -r label input _rest; do
  run_one "$label" "$input" &
  # Bound concurrency: while $JOBS are already running, wait for one to finish.
  while (( $(jobs -rp | wc -l) >= JOBS )); do wait -n; done
done < "$MANIFEST"
wait

# Phase 2 -- classify the recorded outputs (serial, manifest order).
total=0 err=0 full=0 succ=0 root=0 tail=0 fail=0 rod=0
while IFS=$'\t' read -r label input expected_hex succ_bit input_len relpath; do
  total=$((total + 1))
  out="$RUN_DIR/$label.output"
  rc="$(cat "$RUN_DIR/$label.exit" 2>/dev/null || echo 1)"
  if [[ "$rc" != 0 ]]; then
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
  echo "  zisk build:  $ZISKEMU_FLAVOR -- $ZISKEMU_VERSION"
  echo "  jobs:        $JOBS (cpus=$CPUS, ~${PER_PROC_MB} MB/proc budget)"
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

rc=0
if [[ -n "$MIN_SUCC" && "$succ" -lt "$MIN_SUCC" ]]; then
  echo "==> REGRESSION: succ match $succ < --min-succ $MIN_SUCC" >&2; rc=1
fi
if [[ -n "$MIN_FULL" && "$full" -lt "$MIN_FULL" ]]; then
  echo "==> REGRESSION: full match $full < --min-full $MIN_FULL" >&2; rc=1
fi
if [[ -n "$MIN_ROOT" && "$root" -lt "$MIN_ROOT" ]]; then
  echo "==> REGRESSION: root match $root < --min-root $MIN_ROOT" >&2; rc=1
fi
exit $rc
