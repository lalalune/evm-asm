#!/usr/bin/env bash
# div128-v5-model-check.sh — Layer-1 random differential test of the
# `div128Quot_v5` math model against a Nat-level true-quotient reference.
#
# Bead `evm-asm-wbc4i.12` (V5.1.1). The earliest of the V5 layered tests
# (model → inner RV64 → full EVM) — catches math-model bugs in seconds
# before any V5.4 / V5.5 proof effort begins.
#
# Default corpus: PR #7080 + PR #7077 fixed counterexamples + 10000
# pseudo-random uniform + 5000 adversarial wide-uHi inputs. All must
# satisfy the Knuth-A `+1` window `q_true ≤ div128Quot_v5 ≤ q_true + 1`.
#
# Usage:
#   scripts/div128-v5-model-check.sh                  # default: 10k + 5k, seed=42
#   scripts/div128-v5-model-check.sh 50000 25000 7    # custom sizes + seed
#
# Exit:
#   0 — every sample passes the `+1` window
#   1 — at least one sample violates; downstream V5.4 / V5.5 proof work
#       should be blocked until the model is fixed
set -euo pipefail

cd "$(dirname "$0")/.."

N_RANDOM="${1:-10000}"
N_ADVERSARIAL="${2:-5000}"
SEED="${3:-42}"

echo "==> lake build div128-v5-check"
lake build div128-v5-check

echo "==> lake exe div128-v5-check $N_RANDOM $N_ADVERSARIAL $SEED"
lake exe div128-v5-check "$N_RANDOM" "$N_ADVERSARIAL" "$SEED"
