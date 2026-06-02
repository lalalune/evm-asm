#!/usr/bin/env bash
# codegen-zisk-stateless-verdict-check.sh -- verify stateless_verdict_from_ssz
# (bead evm-asm-fhsxz.2.4.2) on REAL EEST fixtures.
#
# The `zisk_stateless_verdict` probe is fed the SAME ziskemu `-i` input the
# stateless guest consumes (SSZ_BASE = 0x40000012), navigates it with the real
# extractors, runs step2_verdict, and emits the verdict bit at OUTPUT+0. We
# compare that bit against the fixture's expected `successful_validation`
# (the manifest's succ_bit). This proves the verdict on REAL input (closing
# the "synthetic-only" gap) and is the de-risk before wiring into the guest
# epilogue.
#
# Reports, per fixture: verdict==expected (MATCH) / verdict!=expected (DIFF).
# A valid block whose verdict the guest cannot yet confirm (tx-bearing,
# non-existent-account, repeat) shows verdict=0 vs exp=1 = a conservative MISS
# (expected; not a soundness failure). A DIFF where verdict=1 vs exp=0 would be
# a FALSE POSITIVE (a real bug) -- flagged loudly.
#
# Usage:
#   codegen-zisk-stateless-verdict-check.sh [--filter SUB] [--limit N]
#     --max-failures N         stop after N ERROR/FALSE-POSITIVE/DIFF results
#     --stop-after-failures N  alias for --max-failures
set -euo pipefail
cd "$(dirname "$0")/.."
REPO_ROOT="$(pwd)"

TAG="${EEST_FIXTURE_TAG:-zkevm@v0.4.0}"
FILTER="eip4895"
LIMIT=30
STEPS="${EEST_STEPS:-50000000}"
MAX_FAILURES=""

usage() {
  cat <<'USAGE'
Usage:
  scripts/codegen-zisk-stateless-verdict-check.sh [options]

Options:
  --filter SUBSTR          only fixtures whose relpath contains SUBSTR
  --limit N                cap to N probe invocations (default 30)
  --steps N                ziskemu max steps (default $EEST_STEPS or 50000000)
  --max-failures N         stop after N ERROR/FALSE-POSITIVE/DIFF results
  --stop-after-failures N  alias for --max-failures
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
    --filter) require_arg "$1" "${2:-}"; FILTER="$2"; shift 2 ;;
    --limit)  require_arg "$1" "${2:-}"; LIMIT="$2";  shift 2 ;;
    --steps)  require_arg "$1" "${2:-}"; STEPS="$2";  shift 2 ;;
    --max-failures|--stop-after-failures) require_arg "$1" "${2:-}"; MAX_FAILURES="$2"; shift 2 ;;
    *) echo "unknown arg: $1" >&2; usage >&2; exit 1 ;;
  esac
done

if ! [[ "$LIMIT" =~ ^[0-9]+$ ]] || [[ "$LIMIT" -lt 1 ]]; then
  echo "--limit must be a positive integer (got: $LIMIT)" >&2
  exit 1
fi
if ! [[ "$STEPS" =~ ^[0-9]+$ ]] || [[ "$STEPS" -lt 1 ]]; then
  echo "--steps must be a positive integer (got: $STEPS)" >&2
  exit 1
fi
if [[ -n "$MAX_FAILURES" ]] && { ! [[ "$MAX_FAILURES" =~ ^[0-9]+$ ]] || [[ "$MAX_FAILURES" -lt 1 ]]; }; then
  echo "--max-failures must be a positive integer when set (got: $MAX_FAILURES)" >&2
  exit 1
fi

ZISKEMU="${ZISKEMU:-}"
if [[ -z "$ZISKEMU" ]]; then
  if command -v ziskemu >/dev/null 2>&1; then ZISKEMU="$(command -v ziskemu)"
  elif [[ -x "$HOME/.zisk/bin/ziskemu" ]]; then ZISKEMU="$HOME/.zisk/bin/ziskemu"
  else echo "ziskemu not found" >&2; exit 1; fi
fi

FX="${EEST_FIXTURES_DIR:-$REPO_ROOT/gen-out/eest-fixtures/$TAG/fixtures/fixtures}"
[[ -d "$FX" ]] || { echo "fixtures not found at $FX (run scripts/eest-fetch-fixtures.sh '$TAG')" >&2; exit 1; }

echo "==> lake build codegen"
lake build codegen >/dev/null
echo "==> emit zisk_stateless_verdict_v2 probe ELF"
lake exe codegen --program zisk_stateless_verdict_v2 --halt linux93 -o gen-out/zisk_stateless_verdict_v2 >/dev/null

RUN_DIR="$REPO_ROOT/gen-out/verdict-run"
rm -rf "$RUN_DIR"; mkdir -p "$RUN_DIR"
echo "==> convert fixtures (tag=$TAG, filter=$FILTER, limit=$LIMIT)"
python3 scripts/eest-stateless-to-input.py --fixtures-dir "$FX" --out-dir "$RUN_DIR" \
  --limit "$LIMIT" --filter "$FILTER"
MANIFEST="$RUN_DIR/manifest.tsv"
[[ -s "$MANIFEST" ]] || { echo "no blocks selected" >&2; exit 1; }

total=0 match=0 miss=0 fp=0 err=0 diff=0 stopEarly=0

failure_limit_reached() {
  [[ -n "$MAX_FAILURES" && $((err + fp + diff)) -ge "$MAX_FAILURES" ]]
}

while IFS=$'\t' read -r label input expected_hex succ_bit input_len relpath; do
  total=$((total + 1))
  out="$RUN_DIR/$label.vout"
  if ! "$ZISKEMU" -e gen-out/zisk_stateless_verdict_v2.elf -i "$input" -o "$out" \
        -n "$STEPS" >/dev/null 2>&1 </dev/null; then
    err=$((err + 1)); echo "  ERROR(exit)   $relpath"
    if failure_limit_reached; then stopEarly=1; break; fi
    continue
  fi
  v="$(od -An -tu1 -j 0 -N 1 "$out" 2>/dev/null | tr -d ' \n')"
  if [[ -z "$v" ]]; then
    err=$((err + 1)); echo "  ERROR(short)  $relpath"
    if failure_limit_reached; then stopEarly=1; break; fi
    continue
  fi
  dbg="$(od -An -v -tu8 -j 8 -N 80 "$out" 2>/dev/null | xargs || true)"
  if [[ "$v" == "$succ_bit" ]]; then
    match=$((match + 1)); echo "  MATCH  verdict=$v exp=$succ_bit dbg=[$dbg]  $relpath"
  elif [[ "$v" == "0" && "$succ_bit" == "1" ]]; then
    miss=$((miss + 1)); echo "  miss   verdict=0 exp=1 (conservative) dbg=[$dbg]  $relpath"
  elif [[ "$v" == "1" && "$succ_bit" == "0" ]]; then
    fp=$((fp + 1)); echo "  ** FALSE POSITIVE ** verdict=1 exp=0 dbg=[$dbg]  $relpath"
    if failure_limit_reached; then stopEarly=1; break; fi
  else
    diff=$((diff + 1))
    echo "  DIFF   verdict=$v exp=$succ_bit dbg=[$dbg]  $relpath"
    if failure_limit_reached; then stopEarly=1; break; fi
  fi
done < "$MANIFEST"

if [[ "$stopEarly" -eq 1 ]]; then
  echo "==> stopped after $((err + fp + diff)) failure(s) (--max-failures $MAX_FAILURES)"
fi
echo "============================================================"
echo "stateless_verdict on real $FILTER fixtures: total=$total"
echo "  MATCH (verdict==expected):        $match"
echo "  conservative miss (v=0 exp=1):    $miss"
echo "  FALSE POSITIVE (v=1 exp=0):       $fp"
echo "  unexpected DIFF:                  $diff"
echo "  errors:                           $err"
if [[ "$fp" -gt 0 ]]; then
  echo "==> FAIL: false positives present (unsound)"; exit 1
fi
if [[ "$match" -eq 0 ]]; then
  echo "==> no exact matches yet (all conservative misses / errors)"; exit 0
fi
echo "==> PASS: $match verdict(s) match real fixtures, 0 false positives"
