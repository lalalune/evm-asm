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
# Usage: codegen-zisk-stateless-verdict-check.sh [--filter SUB] [--limit N]
set -euo pipefail
cd "$(dirname "$0")/.."
REPO_ROOT="$(pwd)"

TAG="${EEST_FIXTURE_TAG:-zkevm@v0.4.0}"
FILTER="eip4895"
LIMIT=30
STEPS="${EEST_STEPS:-50000000}"
while [[ $# -gt 0 ]]; do
  case "$1" in
    --filter) FILTER="$2"; shift 2 ;;
    --limit)  LIMIT="$2";  shift 2 ;;
    --steps)  STEPS="$2";  shift 2 ;;
    *) echo "unknown arg: $1" >&2; exit 1 ;;
  esac
done

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
echo "==> emit zisk_stateless_verdict probe ELF"
lake exe codegen --program zisk_stateless_verdict --halt linux93 -o gen-out/zisk_stateless_verdict >/dev/null

RUN_DIR="$REPO_ROOT/gen-out/verdict-run"
rm -rf "$RUN_DIR"; mkdir -p "$RUN_DIR"
echo "==> convert fixtures (tag=$TAG, filter=$FILTER, limit=$LIMIT)"
python3 scripts/eest-stateless-to-input.py --fixtures-dir "$FX" --out-dir "$RUN_DIR" \
  --limit "$LIMIT" --filter "$FILTER"
MANIFEST="$RUN_DIR/manifest.tsv"
[[ -s "$MANIFEST" ]] || { echo "no blocks selected" >&2; exit 1; }

total=0 match=0 miss=0 fp=0 err=0
while IFS=$'\t' read -r label input expected_hex succ_bit input_len relpath; do
  total=$((total + 1))
  out="$RUN_DIR/$label.vout"
  if ! "$ZISKEMU" -e gen-out/zisk_stateless_verdict.elf -i "$input" -o "$out" \
        -n "$STEPS" >/dev/null 2>&1 </dev/null; then
    err=$((err + 1)); echo "  ERROR(exit)   $relpath"; continue
  fi
  v="$(od -An -tu1 -j 0 -N 1 "$out" 2>/dev/null | tr -d ' \n')"
  [[ -z "$v" ]] && { err=$((err + 1)); echo "  ERROR(short)  $relpath"; continue; }
  if [[ "$v" == "$succ_bit" ]]; then
    match=$((match + 1)); echo "  MATCH  verdict=$v exp=$succ_bit  $relpath"
  elif [[ "$v" == "0" && "$succ_bit" == "1" ]]; then
    miss=$((miss + 1)); echo "  miss   verdict=0 exp=1 (conservative)  $relpath"
  elif [[ "$v" == "1" && "$succ_bit" == "0" ]]; then
    fp=$((fp + 1)); echo "  ** FALSE POSITIVE ** verdict=1 exp=0  $relpath"
  else
    echo "  DIFF   verdict=$v exp=$succ_bit  $relpath"
  fi
done < "$MANIFEST"

echo "============================================================"
echo "stateless_verdict on real $FILTER fixtures: total=$total"
echo "  MATCH (verdict==expected):        $match"
echo "  conservative miss (v=0 exp=1):    $miss"
echo "  FALSE POSITIVE (v=1 exp=0):       $fp"
echo "  errors:                           $err"
if [[ "$fp" -gt 0 ]]; then
  echo "==> FAIL: false positives present (unsound)"; exit 1
fi
if [[ "$match" -eq 0 ]]; then
  echo "==> no exact matches yet (all conservative misses / errors)"; exit 0
fi
echo "==> PASS: $match verdict(s) match real fixtures, 0 false positives"
