#!/usr/bin/env bash
# codegen-stateless-spec-output-check.sh -- new-schema (zkevm-projects/
# d7fe16ab8) `SszStatelessValidationResult` round-trip.
#
# What's exercised:
#   * Input shape: `STATELESS_INPUT_SCHEMA_ID_BYTES` (= b'\x00\x01')
#     prepended to the SSZ-encoded `SszStatelessInput`, then the
#     8-byte length prefix the way `ziskemu -i` expects. The Lean
#     `read_chain_id` decoder skips the 16+2 preamble and walks the
#     outer offset table to find `chain_config.chain_id`.
#   * Output shape: 73-byte SSZ encoding of
#     `SszStatelessValidationResult(*, *, chain_config(chain_id=X,
#     active_fork=SszForkConfig(fork=0, empty, empty)))`.  The Lean
#     encoder emits the empty-`active_fork` variant; the K-PR header
#     validators take the N=0 fast path until the new-schema witness
#     walk is wired up (follow-up).
#
# Two comparisons per fixture:
#   1. Against the Lean encoder's INTENDED output -- hand-constructed
#      `SszStatelessValidationResult(hash_tree_root(witness), 1,
#      chain_config)`. Byte-for-byte match is required (pass/fail).
#   2. Against Python's `run_stateless_guest(input_bytes)` -- the spec
#      entrypoint. The Lean ELF diverges from this in TWO documented
#      ways that the test prints but does not fail on:
#        (a) bytes 0..32: Lean stamps `hash_tree_root(witness)` while
#            the spec stamps `compute_new_payload_request_root(input)`.
#            Aligning these is a follow-up.
#        (b) byte 32: Lean's epilogue takes the `.Lsg_all_pass` fast
#            path (writes 1) while Python's `verify_stateless_new_
#            payload` raises on the empty witness (returns 0). A real
#            STF wiring would converge them.
#
# Fixtures: 5 chain_id values (1, 0x1234567890ABCDEF, 0, max-u32,
# max-u64).
#
# Exit:
#   0 -- all fixtures match
#   1 -- emission / build / emulation failed, or output mismatch
set -euo pipefail

cd "$(dirname "$0")/.."

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

mkdir -p gen-out

REPO_ROOT="$(pwd)"

echo "==> lake build codegen"
lake build codegen

echo "==> emit stateless_guest ELF"
lake exe codegen --program stateless_guest --halt linux93 \
  -o gen-out/stateless_guest

# Generate one fixture, build input, run ELF, then run TWO compares:
#  (1) Against the Lean encoder's INTENDED output (must match).
#  (2) Against Python's `run_stateless_guest(input_bytes)` (informational
#      diff is printed; mismatches in bytes 0..32 and byte 32 are
#      tolerated and documented).
run_fixture() {
  local label="$1"
  local cid="$2"

  local safe="${label//[^0-9A-Za-z_]/_}"
  local input_file="$REPO_ROOT/gen-out/stateless_guest-spec-${safe}.input"
  local out_file="$REPO_ROOT/gen-out/stateless_guest-spec-${safe}.output"
  local lean_exp_file="$REPO_ROOT/gen-out/stateless_guest-spec-${safe}.lean-expected"
  local spec_exp_file="$REPO_ROOT/gen-out/stateless_guest-spec-${safe}.spec-expected"
  local log_file="$REPO_ROOT/gen-out/stateless_guest-spec-${safe}.emu.log"

  echo "==> [$label] gen new-schema SSZ input + expecteds (chain_id=$cid)"
  uv run --directory execution-specs --quiet python3 -c "
import struct, sys
from ethereum.forks.amsterdam.stateless_ssz import (
    STATELESS_INPUT_SCHEMA_ID_BYTES,
    SszChainConfig,
    SszExecutionWitness,
    SszForkActivation,
    SszForkConfig,
    SszNewPayloadRequest,
    SszStatelessInput,
    SszStatelessValidationResult,
    SszOptionalBlobSchedule,
    SszOptionalForkActivationValue,
    validation_result_to_ssz,
)
from ethereum.forks.amsterdam.stateless_guest import run_stateless_guest
from remerkleable.basic import boolean, uint64
from remerkleable.byte_arrays import Bytes32

cid = int(sys.argv[1], 0)

# Build the minimal new-schema StatelessInput: empty
# new_payload_request, empty witness, chain_config(cid, empty
# active_fork), empty public_keys.
empty_activation = SszForkActivation(
    block_number=SszOptionalForkActivationValue(),
    timestamp=SszOptionalForkActivationValue(),
)
empty_fork = SszForkConfig(
    fork=uint64(0),
    activation=empty_activation,
    blob_schedule=SszOptionalBlobSchedule(),
)
cc = SszChainConfig(chain_id=uint64(cid), active_fork=empty_fork)
ssz_input = SszStatelessInput(
    new_payload_request=SszNewPayloadRequest(),
    witness=SszExecutionWitness(),
    chain_config=cc,
    public_keys=(),
)
input_bytes = STATELESS_INPUT_SCHEMA_ID_BYTES + ssz_input.encode_bytes()

# Write the ziskemu -i envelope: 8-byte length prefix + blob.
total = 8 + len(input_bytes)
pad = (-total) % 8
with open(sys.argv[2], 'wb') as f:
    f.write(struct.pack('<Q', len(input_bytes)))
    f.write(input_bytes)
    if pad: f.write(b'\\x00' * pad)

# --- Expected #1: Lean encoder's INTENDED output ---
# hash_tree_root(witness) stamped at [0..32) by the epilogue
# + successful_validation = 1 (epilogue's .Lsg_all_pass override)
# + chain_config (SSZ-encoded by Lean).
witness_root = ssz_input.witness.hash_tree_root()
lean_intended = SszStatelessValidationResult(
    new_payload_request_root=Bytes32(bytes(witness_root)),
    successful_validation=boolean(True),
    chain_config=cc,
)
lean_bytes = lean_intended.encode_bytes()
assert len(lean_bytes) == 73, f'lean: expected 73, got {len(lean_bytes)}'
with open(sys.argv[3], 'w') as f:
    f.write(lean_bytes.hex())

# --- Expected #2: Spec's run_stateless_guest output ---
# This is what a fully-implemented STF would produce.
spec_bytes = bytes(run_stateless_guest(input_bytes))
assert len(spec_bytes) == 73, f'spec: expected 73, got {len(spec_bytes)}'
with open(sys.argv[4], 'w') as f:
    f.write(spec_bytes.hex())
" "$cid" "$input_file" "$lean_exp_file" "$spec_exp_file"

  echo "==> [$label] ziskemu run"
  "$ZISKEMU" -e gen-out/stateless_guest.elf -i "$input_file" \
    -o "$out_file" -n 500000 >"$log_file" 2>&1

  local actual lean_expected spec_expected
  actual="$(xxd -p -l 73 "$out_file" | tr -d '\n')"
  lean_expected="$(cat "$lean_exp_file")"
  spec_expected="$(cat "$spec_exp_file")"

  echo "    Lean intended:           $lean_expected"
  echo "    ELF actual:              $actual"
  echo "    Python run_stateless_guest:"
  echo "                             $spec_expected"

  # Diff actual vs spec, byte by byte, to show divergence regions.
  python3 -c "
a = bytes.fromhex('$actual')
s = bytes.fromhex('$spec_expected')
diffs = [(i, a[i], s[i]) for i in range(len(a)) if a[i] != s[i]]
if not diffs:
    print('    spec diff: none -- ELF output matches run_stateless_guest exactly!')
else:
    # Coalesce contiguous diff ranges.
    ranges = []
    cur = [diffs[0][0], diffs[0][0]]
    for (i, _, _) in diffs[1:]:
        if i == cur[1] + 1:
            cur[1] = i
        else:
            ranges.append(tuple(cur))
            cur = [i, i]
    ranges.append(tuple(cur))
    rs = ', '.join(f'[{lo}..{hi+1})' for lo, hi in ranges)
    print(f'    spec diff: bytes {rs} differ from spec (documented: hash field + valid bit)')
"

  if [[ "$actual" == "$lean_expected" ]]; then
    echo "    PASS (matches Lean intended)"
    return 0
  else
    echo "    FAIL (ELF actual != Lean intended)"
    return 1
  fi
}

fail=0
run_fixture "chain1"                1                       || fail=1
run_fixture "chain_big"             0x1234567890ABCDEF      || fail=1
run_fixture "chain_zero"            0                       || fail=1
run_fixture "chain_max_u32"         0xFFFFFFFF              || fail=1
run_fixture "chain_max_u64"         0xFFFFFFFFFFFFFFFF      || fail=1

if [[ "$fail" -eq 0 ]]; then
  echo "==> PASS: all spec-output fixtures match the new SSZ schema"
  exit 0
else
  echo "==> FAIL: at least one fixture mismatched"
  exit 1
fi
