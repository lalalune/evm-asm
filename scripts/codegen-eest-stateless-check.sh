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
#     --skip N           skip first N selected stateless blocks after filtering
#     --limit N          cap to N guest invocations (default 50)
#     --filter SUBSTR    only fixtures whose relpath contains SUBSTR
#     --steps N          ziskemu max steps (default $EEST_STEPS or 50000000)
#     --jobs N|auto      parallel ziskemu jobs (default $EEST_JOBS or auto)
#     --max-failures N   stop after N FAIL/ERROR results (default: disabled)
#     --stop-after-failures N
#                        alias for --max-failures
#     --quiet-passes     suppress per-case PASS(full) lines
#     --job-mem-mib N|auto
#                        memory budget per ziskemu job (default $EEST_JOB_MEM_MIB
#                        or auto). Auto is derived from the ziskemu build:
#                        stock builds budget ~7000 MiB/process; patched lowmem
#                        builds advertising PATCHED-lowmem budget 1024 MiB/process
#                        for this stateless guest workload.
#                        CPU cap uses one core/job on patched builds and four
#                        cores/job on stock builds unless EEST_JOB_CPU_THREADS is set.
#     --min-succ N       exit 1 if fewer than N succ-bit matches (regression gate)
#     --min-full N       exit 1 if fewer than N full (105-byte) matches (regression gate)
#     --min-root N       exit 1 if fewer than N root matches (regression gate)
#     --tag TAG          EEST fixture tag (default $EEST_FIXTURE_TAG or zkevm@v0.4.0)
#
# Exit:
#   0 -- ran to completion (baseline mode), or all --min-* thresholds met
#   1 -- build/convert failure, no fixtures, or a --min-{succ,full,root} regression
set -euo pipefail

cd "$(dirname "$0")/.."
REPO_ROOT="$(pwd)"

ALL=0
SKIP=0
LIMIT=50
FILTER=""
# Default step cap. ziskemu stops at the guest's halt, so this only bounds
# runaway/very-large runs -- raised to 50M so many-deposit / large-tx blocks
# (whose NPR-root merkleization is sha256-heavy) complete; normal blocks
# halt long before this and are not slowed.
STEPS="${EEST_STEPS:-50000000}"
JOBS="${EEST_JOBS:-auto}"
JOB_MEM_MIB="${EEST_JOB_MEM_MIB:-auto}"
JOB_CPU_THREADS="${EEST_JOB_CPU_THREADS:-auto}"
MEM_RESERVE_MIB="${EEST_MEM_RESERVE_MIB:-4096}"
MAX_FAILURES=""
RUN_DIR_OVERRIDE=""
QUIET_PASSES="${EEST_QUIET_PASSES:-0}"
MIN_SUCC=""
MIN_FULL=""
MIN_ROOT=""
TAG="${EEST_FIXTURE_TAG:-zkevm@v0.4.0}"
NO_BUILD="${EEST_NO_BUILD:-0}"

usage() {
  cat <<'USAGE'
Usage:
  scripts/codegen-eest-stateless-check.sh [options]

Options:
  --all                    run every stateless block (slow); default: smoke subset
  --skip N                 skip first N selected stateless blocks after filtering
  --limit N                cap to N guest invocations (default 50)
  --filter SUBSTR          only fixtures whose relpath contains SUBSTR
  --steps N                ziskemu max steps (default $EEST_STEPS or 50000000)
  --jobs N|auto            parallel ziskemu jobs (default $EEST_JOBS or auto)
  --max-failures N         stop after N FAIL/ERROR results
  --stop-after-failures N  alias for --max-failures
  --quiet-passes           suppress per-case PASS(full) lines
  --show-passes            print per-case PASS(full) lines, overriding EEST_QUIET_PASSES
  --job-mem-mib N|auto     memory budget per ziskemu job
  --min-succ N             exit 1 if fewer than N succ-bit matches
  --min-full N             exit 1 if fewer than N full matches
  --min-root N             exit 1 if fewer than N root matches
  --tag TAG                EEST fixture tag (default $EEST_FIXTURE_TAG or zkevm@v0.4.0)
  --no-build               skip lake build + ELF emit (reuse existing gen-out/stateless_guest.elf)
  --run-dir DIR            use DIR instead of gen-out/eest-run (enables parallel invocations)
  -h, --help               show this help
USAGE
}

require_arg() {
  local opt="$1"
  if [[ $# -lt 2 || -z "${2:-}" ]]; then
    echo "$opt requires an argument" >&2
    usage >&2
    exit 1
  fi
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    -h|--help) usage; exit 0 ;;
    --all) ALL=1; shift ;;
    --skip) require_arg "$1" "${2:-}"; SKIP="$2"; shift 2 ;;
    --limit) require_arg "$1" "${2:-}"; LIMIT="$2"; shift 2 ;;
    --filter) require_arg "$1" "${2:-}"; FILTER="$2"; shift 2 ;;
    --steps) require_arg "$1" "${2:-}"; STEPS="$2"; shift 2 ;;
    --jobs) require_arg "$1" "${2:-}"; JOBS="$2"; shift 2 ;;
    --max-failures|--stop-after-failures) require_arg "$1" "${2:-}"; MAX_FAILURES="$2"; shift 2 ;;
    --quiet-passes) QUIET_PASSES=1; shift ;;
    --show-passes) QUIET_PASSES=0; shift ;;
    --job-mem-mib) require_arg "$1" "${2:-}"; JOB_MEM_MIB="$2"; shift 2 ;;
    --min-succ) require_arg "$1" "${2:-}"; MIN_SUCC="$2"; shift 2 ;;
    --min-full) require_arg "$1" "${2:-}"; MIN_FULL="$2"; shift 2 ;;
    --min-root) require_arg "$1" "${2:-}"; MIN_ROOT="$2"; shift 2 ;;
    --tag) require_arg "$1" "${2:-}"; TAG="$2"; shift 2 ;;
    --run-dir) require_arg "$1" "${2:-}"; RUN_DIR_OVERRIDE="$2"; shift 2 ;;
    --no-build) NO_BUILD=1; shift ;;
    *) echo "unknown arg: $1" >&2; usage >&2; exit 1 ;;
  esac
done

if ! [[ "$SKIP" =~ ^[0-9]+$ ]]; then
  echo "--skip must be a nonnegative integer (got: $SKIP)" >&2
  exit 1
fi
if [[ "$JOBS" != "auto" ]] && { ! [[ "$JOBS" =~ ^[0-9]+$ ]] || [[ "$JOBS" -lt 1 ]]; }; then
  echo "--jobs must be a positive integer or auto (got: $JOBS)" >&2
  exit 1
fi
if [[ "$JOB_MEM_MIB" != "auto" ]] && { ! [[ "$JOB_MEM_MIB" =~ ^[0-9]+$ ]] || [[ "$JOB_MEM_MIB" -lt 1 ]]; }; then
  echo "--job-mem-mib must be a positive integer or auto (got: $JOB_MEM_MIB)" >&2
  exit 1
fi
if [[ "$JOB_CPU_THREADS" != "auto" ]] && { ! [[ "$JOB_CPU_THREADS" =~ ^[0-9]+$ ]] || [[ "$JOB_CPU_THREADS" -lt 1 ]]; }; then
  echo "EEST_JOB_CPU_THREADS must be a positive integer or auto (got: $JOB_CPU_THREADS)" >&2
  exit 1
fi
if [[ -n "$MAX_FAILURES" ]] && { ! [[ "$MAX_FAILURES" =~ ^[0-9]+$ ]] || [[ "$MAX_FAILURES" -lt 1 ]]; }; then
  echo "--max-failures must be a positive integer when set (got: $MAX_FAILURES)" >&2
  exit 1
fi
if ! [[ "$QUIET_PASSES" =~ ^(0|1|true|false|yes|no)$ ]]; then
  echo "EEST_QUIET_PASSES must be 0/1/true/false/yes/no (got: $QUIET_PASSES)" >&2
  exit 1
fi
case "$QUIET_PASSES" in
  1|true|yes) QUIET_PASSES=1 ;;
  *) QUIET_PASSES=0 ;;
esac
if ! [[ "$MEM_RESERVE_MIB" =~ ^[0-9]+$ ]]; then
  echo "EEST_MEM_RESERVE_MIB must be a nonnegative integer (got: $MEM_RESERVE_MIB)" >&2
  exit 1
fi

cleanup_children() {
  local pids
  pids="$(jobs -pr || true)"
  if [[ -n "$pids" ]]; then
    # shellcheck disable=SC2086
    kill $pids 2>/dev/null || true
    wait 2>/dev/null || true
  fi
}
trap 'cleanup_children; exit 130' INT TERM HUP

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
# the float library into its own array; tiny ELFs measure around 30 MB RSS, while
# the stateless guest measures around 700 MB RSS on real fixtures. We size this
# harness for the stateless workload.
ZISKEMU_VERSION="$("$ZISKEMU" --version 2>/dev/null || echo unknown)"
if [[ "$ZISKEMU_VERSION" == *PATCHED-lowmem* ]]; then
  ZISKEMU_FLAVOR="patched-lowmem"
  ZISKEMU_AUTO_JOB_MEM_MIB=1024
  ZISKEMU_AUTO_JOB_CPU_THREADS=1
else
  ZISKEMU_FLAVOR="stock"
  ZISKEMU_AUTO_JOB_MEM_MIB=7000
  ZISKEMU_AUTO_JOB_CPU_THREADS=4
fi
if [[ "$JOB_MEM_MIB" == "auto" ]]; then
  JOB_MEM_MIB="$ZISKEMU_AUTO_JOB_MEM_MIB"
fi
if [[ "$JOB_CPU_THREADS" == "auto" ]]; then
  JOB_CPU_THREADS="$ZISKEMU_AUTO_JOB_CPU_THREADS"
fi

compute_job_cap() {
  local mem_avail_kib mem_avail_mib mem_cap ncpu cpu_cap cap
  mem_avail_kib="$(awk '/MemAvailable:/ {print $2}' /proc/meminfo 2>/dev/null || true)"
  if [[ -z "$mem_avail_kib" ]]; then
    mem_cap=1
  else
    mem_avail_mib=$((mem_avail_kib / 1024))
    if [[ "$mem_avail_mib" -le "$MEM_RESERVE_MIB" ]]; then
      mem_cap=1
    else
      mem_cap=$(((mem_avail_mib - MEM_RESERVE_MIB) / JOB_MEM_MIB))
      [[ "$mem_cap" -lt 1 ]] && mem_cap=1
    fi
  fi
  ncpu="$(nproc 2>/dev/null || echo 1)"
  cpu_cap=$((ncpu / JOB_CPU_THREADS))
  [[ "$cpu_cap" -lt 1 ]] && cpu_cap=1
  cap="$mem_cap"
  [[ "$cpu_cap" -lt "$cap" ]] && cap="$cpu_cap"
  echo "$cap"
}

CPUS="$(nproc 2>/dev/null || echo 1)"
JOB_CAP="$(compute_job_cap)"
if [[ "$JOBS" == "auto" ]]; then
  JOBS="$JOB_CAP"
elif [[ "$JOBS" -gt "$JOB_CAP" ]]; then
  echo "==> requested --jobs $JOBS capped to $JOB_CAP (job_mem=${JOB_MEM_MIB}MiB, reserve=${MEM_RESERVE_MIB}MiB, cpu_threads/job=$JOB_CPU_THREADS)" >&2
  JOBS="$JOB_CAP"
fi

echo "==> ziskemu: $ZISKEMU"
echo "    version: $ZISKEMU_VERSION"
echo "    flavor:  $ZISKEMU_FLAVOR (${JOB_MEM_MIB} MiB/proc budget) -> jobs=$JOBS (cpus=$CPUS)"

# --- locate fixtures --------------------------------------------------------
FX="${EEST_FIXTURES_DIR:-$REPO_ROOT/gen-out/eest-fixtures/$TAG/fixtures/fixtures}"
if [[ ! -d "$FX" ]]; then
  echo "EEST fixtures not found at: $FX" >&2
  echo "  run: scripts/eest-fetch-fixtures.sh '$TAG'" >&2
  exit 1
fi

mkdir -p gen-out

if [[ "$NO_BUILD" -eq 0 ]]; then
  echo "==> lake build codegen"
  lake build codegen

  echo "==> emit stateless_guest ELF"
  lake exe codegen --program stateless_guest --halt linux93 -o gen-out/stateless_guest
else
  echo "==> skipping build (--no-build)"
fi

# --- convert fixtures -> ziskemu inputs + manifest --------------------------
RUN_DIR="${RUN_DIR_OVERRIDE:-$REPO_ROOT/gen-out/eest-run}"
rm -rf "$RUN_DIR"
mkdir -p "$RUN_DIR"
conv_args=(--fixtures-dir "$FX" --out-dir "$RUN_DIR")
[[ "$SKIP" != "0" ]] && conv_args+=(--skip "$SKIP")
[[ "$ALL" -eq 0 ]] && conv_args+=(--limit "$LIMIT")
[[ -n "$FILTER" ]] && conv_args+=(--filter "$FILTER")
selection="$([[ $ALL -eq 1 ]] && echo all || echo "limit=$LIMIT")"
[[ "$SKIP" != "0" ]] && selection="$selection, skip=$SKIP"
[[ -n "$FILTER" ]] && selection="$selection, filter=$FILTER"
echo "==> convert fixtures (tag=$TAG, $selection)"
python3 scripts/eest-stateless-to-input.py "${conv_args[@]}"

MANIFEST="$RUN_DIR/manifest.tsv"
[[ -s "$MANIFEST" ]] || { echo "no stateless blocks selected" >&2; exit 1; }
mapfile -t manifestLines < "$MANIFEST"
selectedCount="${#manifestLines[@]}"

run_case() {
  local line="$1"
  local label input expected_hex succ_bit input_len relpath
  IFS=$'\t' read -r label input expected_hex succ_bit input_len relpath <<< "$line"
  local out="$RUN_DIR/$label.output"
  local log="$RUN_DIR/$label.emu.log"
  local result="$RUN_DIR/$label.result.tsv"
  local tmp_result="$result.tmp.$$"
  local actual_hex

  if ! "$ZISKEMU" -e gen-out/stateless_guest.elf -i "$input" -o "$out" \
        -n "$STEPS" >"$log" 2>&1 </dev/null; then
    printf 'ERROR\texit\n' > "$tmp_result"
    mv "$tmp_result" "$result"
    return 0
  fi
  actual_hex="$(xxd -p -l 105 "$out" 2>/dev/null | tr -d '\n' || true)"
  if [[ "${#actual_hex}" -lt 210 ]]; then
    printf 'ERROR\tshort:%s\n' "${#actual_hex}" > "$tmp_result"
    mv "$tmp_result" "$result"
    return 0
  fi
  printf 'OK\t%s\n' "$actual_hex" > "$tmp_result"
  mv "$tmp_result" "$result"
}

wait_for_one_worker() {
  local rc
  set +e
  wait -n
  rc=$?
  set -e
  return "$rc"
}

# --- classify ---------------------------------------------------------------
# The 105-byte SszStatelessValidationResult decomposes into three
# independently-checkable regions, so we report each separately to show
# exactly where the guest stands (not just full-vs-not):
#   root [0:32]   = new_payload_request_root  (hex chars 0..64)
#   succ [32]     = successful_validation     (hex chars 64..66)
#   tail [33:105] = u32 offset (=37) + 68-byte chain_config (hex 66..210)
declare -A classifiedLabels=()
total=0 err=0 full=0 succ=0 root=0 tail=0 fail=0 rod=0

classify_case_result() {
  local line="$1"
  local require_result="${2:-0}"
  local label input expected_hex succ_bit input_len relpath result status actual_hex exp r s t
  IFS=$'\t' read -r label input expected_hex succ_bit input_len relpath <<< "$line"
  if [[ -n "${classifiedLabels[$label]+x}" ]]; then
    return 0
  fi
  result="$RUN_DIR/$label.result.tsv"
  if [[ ! -f "$result" ]]; then
    if [[ "$require_result" -eq 0 ]]; then
      return 1
    fi
    classifiedLabels["$label"]=1
    total=$((total + 1))
    err=$((err + 1))
    echo "  ERROR(missing) $relpath"
    return 0
  fi
  classifiedLabels["$label"]=1
  total=$((total + 1))
  IFS=$'\t' read -r status actual_hex < "$result"
  if [[ "$status" != "OK" ]]; then
    err=$((err + 1))
    case "$actual_hex" in
      exit) echo "  ERROR(exit)   $relpath" ;;
      short:*) echo "  ERROR(short)  $relpath (${actual_hex#short:} hex chars)" ;;
      *) echo "  ERROR($actual_hex) $relpath" ;;
    esac
    return 0
  fi
  exp="${expected_hex:0:210}"

  # Per-region matches.
  [[ "${actual_hex:0:64}"   == "${exp:0:64}"   ]] && { root=$((root + 1)); r=root; } || r=----
  [[ "${actual_hex:64:2}"   == "${exp:64:2}"   ]] && { succ=$((succ + 1)); s=succ; } || s=----
  [[ "${actual_hex:66:144}" == "${exp:66:144}" ]] && { tail=$((tail + 1)); t=tail; } || t=----

  if [[ "$actual_hex" == "$exp" ]]; then
    full=$((full + 1))
    [[ "$QUIET_PASSES" -eq 1 ]] || echo "  PASS(full)        $relpath"
  else
    fail=$((fail + 1))
    # root-only diff: succ + tail already match, ONLY the 32-byte root
    # differs -- i.e. this block is exactly one field (the NPR root) from
    # a full match. This is the precise "distance to crown jewel" metric.
    [[ "$s" == "succ" && "$t" == "tail" && "$r" == "----" ]] && rod=$((rod + 1))
    echo "  FAIL [$r/$s/$t]  $relpath (succ guest=${actual_hex:64:2} exp=${exp:64:2})"
  fi
  return 0
}

classify_completed_results() {
  local line
  for line in "${manifestLines[@]}"; do
    classify_case_result "$line" 0 || true
    if failure_limit_reached; then
      return 0
    fi
  done
}

classify_missing_results() {
  local line
  for line in "${manifestLines[@]}"; do
    classify_case_result "$line" 1 || true
  done
}

failure_limit_reached() {
  [[ -n "$MAX_FAILURES" && $((fail + err)) -ge "$MAX_FAILURES" ]]
}

stopEarly=0
worker_fail=0
run_note=""
[[ -n "$MAX_FAILURES" ]] && run_note=", max_failures=$MAX_FAILURES"
echo "==> run stateless_guest on $selectedCount input(s) (jobs=$JOBS$run_note)"
if [[ "$JOBS" -eq 1 ]]; then
  for line in "${manifestLines[@]}"; do
    run_case "$line"
    classify_case_result "$line" 1
    if failure_limit_reached; then
      stopEarly=1
      break
    fi
  done
else
  active=0
  nextLine=0
  while [[ "$nextLine" -lt "$selectedCount" || "$active" -gt 0 ]]; do
    while [[ "$nextLine" -lt "$selectedCount" && "$active" -lt "$JOBS" ]]; do
      if failure_limit_reached; then
        break
      fi
      run_case "${manifestLines[$nextLine]}" &
      active=$((active + 1))
      nextLine=$((nextLine + 1))
    done

    if failure_limit_reached; then
      stopEarly=1
      cleanup_children
      active=0
      classify_completed_results
      break
    fi
    if [[ "$active" -eq 0 ]]; then
      break
    fi

    wait_for_one_worker || worker_fail=1
    active=$((active - 1))
    classify_completed_results
    if failure_limit_reached; then
      stopEarly=1
      cleanup_children
      active=0
      classify_completed_results
      break
    fi
  done
  if [[ "$worker_fail" -ne 0 ]]; then
    echo "==> warning: at least one worker exited unexpectedly; classifying available results" >&2
  fi
fi
if [[ "$stopEarly" -eq 0 ]]; then
  classify_missing_results
fi
if [[ "$stopEarly" -eq 1 ]]; then
  echo "==> stopped after $((fail + err)) failure(s) (--max-failures $MAX_FAILURES)"
fi

ran=$((total - err))
# --- summary + baseline file ------------------------------------------------
BASELINE="$REPO_ROOT/gen-out/eest-baseline.txt"
{
  echo "EEST stateless-guest baseline"
  echo "  generated:   $(date -u '+%Y-%m-%dT%H:%M:%SZ')"
  echo "  fixture tag: $TAG"
  echo "  selection:   $selection"
  echo "  ziskemu:     $ZISKEMU (steps=$STEPS)"
  echo "  zisk build:  $ZISKEMU_FLAVOR -- $ZISKEMU_VERSION"
  echo "  jobs:        $JOBS (cpus=$CPUS, ${JOB_MEM_MIB} MiB/proc budget)"
  echo "  selected:    $selectedCount"
  [[ "$stopEarly" -eq 1 ]] && echo "  stopped:     after $((fail + err)) failure(s) (--max-failures $MAX_FAILURES)"
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
