#!/usr/bin/env bash
# codegen-stateless-spec-output-check.sh -- new-schema (zkevm-projects/
# d7fe16ab8) `SszStatelessValidationResult` byte-for-byte round-trip.
#
# What's exercised:
#   * Input shape: `STATELESS_INPUT_SCHEMA_ID_BYTES` (= b'\x00\x01')
#     prepended to the SSZ-encoded `SszStatelessInput`, then the
#     8-byte length prefix the way `ziskemu -i` expects. The Lean
#     `read_chain_id` decoder skips the 16+2 preamble and walks the
#     outer offset table to find `chain_config.chain_id`.
#   * Output shape: 73-byte SSZ encoding of
#     `SszStatelessValidationResult(zero_hash, valid=1, chain_config(
#     chain_id=X, active_fork=SszForkConfig(fork=0, empty, empty)))`.
#     The Lean encoder always emits the empty-`active_fork` variant
#     (header validation is not yet wired through the new outer
#     offset table -- so the encoder fast-paths to `valid=1` via the
#     epilogue's `.Lsg_all_pass` branch, and the K-PR header
#     validators do not run).
#
# The stateless_guest epilogue overwrites bytes 0..32 with
# `hash_tree_root(witness)` -- we compute the expected hash in
# Python with the spec's reference library.
#
# Fixtures: 5 (a single chain_id sweep + an empty-witness baseline).
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

# Generate one fixture (chain_id, label) -> input file + expected hex
# of the 73-byte output. Driven by execution-specs reference library.
run_fixture() {
  local label="$1"
  local cid="$2"

  local safe="${label//[^0-9A-Za-z_]/_}"
  local input_file="$REPO_ROOT/gen-out/stateless_guest-spec-${safe}.input"
  local out_file="$REPO_ROOT/gen-out/stateless_guest-spec-${safe}.output"
  local exp_file="$REPO_ROOT/gen-out/stateless_guest-spec-${safe}.expected"
  local log_file="$REPO_ROOT/gen-out/stateless_guest-spec-${safe}.emu.log"

  echo "==> [$label] gen new-schema SSZ input (chain_id=$cid)"
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
)
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
blob = STATELESS_INPUT_SCHEMA_ID_BYTES + ssz_input.encode_bytes()

# Write the ziskemu -i envelope: 8-byte length prefix + blob.
# Padded to multiple of 8 bytes (ziskemu requirement).
total = 8 + len(blob)
pad = (-total) % 8
with open(sys.argv[2], 'wb') as f:
    f.write(struct.pack('<Q', len(blob)))
    f.write(blob)
    if pad: f.write(b'\\x00' * pad)

# Build the expected 73-byte output: zero hash + valid=1 + chain_id +
# empty active_fork tail.  (The Lean epilogue overwrites bytes 0..32
# with hash_tree_root(witness); we compute that separately for diff.)
expected_vr = SszStatelessValidationResult(
    new_payload_request_root=Bytes32(b'\\x00' * 32),
    successful_validation=boolean(True),
    chain_config=cc,
)
expected = expected_vr.encode_bytes()
assert len(expected) == 73, f'expected 73 bytes, got {len(expected)}'
with open(sys.argv[3], 'w') as f:
    f.write(expected.hex())

# Compute hash_tree_root(witness) -- the epilogue stamps it at bytes
# 0..32 of the actual output, replacing the zero hash above.
witness_root = ssz_input.witness.hash_tree_root()
hash_hex = bytes(witness_root).hex()
print(hash_hex)
" "$cid" "$input_file" "$exp_file" > "$exp_file.hash"

  local witness_hash
  witness_hash="$(cat "$exp_file.hash")"

  echo "==> [$label] ziskemu run"
  "$ZISKEMU" -e gen-out/stateless_guest.elf -i "$input_file" \
    -o "$out_file" -n 500000 >"$log_file" 2>&1

  local expected_with_hash actual
  # Patch the expected: bytes 0..32 = witness_hash (epilogue stamps),
  # bytes 32..73 = remainder of the SSZ-encoded result.
  expected_with_hash="${witness_hash}$(tail -c +65 "$exp_file")"
  actual="$(xxd -p -l 73 "$out_file" | tr -d '\n')"

  echo "    expected: $expected_with_hash"
  echo "    actual:   $actual"

  if [[ "$actual" == "$expected_with_hash" ]]; then
    echo "    PASS"
    return 0
  else
    echo "    FAIL"
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
