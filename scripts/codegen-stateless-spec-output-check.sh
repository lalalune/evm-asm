#!/usr/bin/env bash
# codegen-stateless-spec-output-check.sh -- new-schema (zkevm-projects/
# d7fe16ab8) `SszStatelessValidationResult` round-trip.
#
# Drives the ELF against the spec entrypoint run_stateless_guest()
# directly and requires a byte-for-byte match.
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
# How the ELF achieves spec-match in the empty-input regime:
#   (a) The decoder stub leaves `x11 = 0`; the encoder writes
#       `successful_validation = 0` (matching the spec's
#       `verify_stateless_new_payload(empty) == False` outcome --
#       `validate_headers([])` raises).
#   (b) The epilogue stamps `compute_new_payload_request_root(empty)`
#       (a 32-byte constant `empty_npr_root` in `.data`) at OUTPUT
#       bytes [0..32). This is the spec's hash field for any input
#       whose `new_payload_request` is empty.
# A future PR generalising `hash_tree_root(SszNewPayloadRequest)` to
# non-empty payloads will switch this stamp to a real computation.
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

# Generate one fixture, build input, run ELF, diff against
# run_stateless_guest byte-for-byte.
run_fixture() {
  local label="$1"
  local cid="$2"

  local safe="${label//[^0-9A-Za-z_]/_}"
  local input_file="$REPO_ROOT/gen-out/stateless_guest-spec-${safe}.input"
  local out_file="$REPO_ROOT/gen-out/stateless_guest-spec-${safe}.output"
  local spec_exp_file="$REPO_ROOT/gen-out/stateless_guest-spec-${safe}.spec-expected"
  local log_file="$REPO_ROOT/gen-out/stateless_guest-spec-${safe}.emu.log"

  echo "==> [$label] gen new-schema SSZ input + spec expected (chain_id=$cid)"
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
    SszOptionalBlobSchedule,
    SszOptionalForkActivationValue,
)
from ethereum.forks.amsterdam.stateless_guest import run_stateless_guest
from remerkleable.basic import uint64

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

# Expected = Python run_stateless_guest output -- the spec entrypoint.
# The Lean ELF should match this byte-for-byte for the current
# empty-input regime.
spec_bytes = bytes(run_stateless_guest(input_bytes))
assert len(spec_bytes) == 73, f'spec: expected 73, got {len(spec_bytes)}'
with open(sys.argv[3], 'w') as f:
    f.write(spec_bytes.hex())
" "$cid" "$input_file" "$spec_exp_file"

  echo "==> [$label] ziskemu run"
  "$ZISKEMU" -e gen-out/stateless_guest.elf -i "$input_file" \
    -o "$out_file" -n 500000 >"$log_file" 2>&1

  local actual spec_expected
  actual="$(xxd -p -l 73 "$out_file" | tr -d '\n')"
  spec_expected="$(cat "$spec_exp_file")"

  echo "    ELF actual:              $actual"
  echo "    Python run_stateless_guest:"
  echo "                             $spec_expected"

  if [[ "$actual" == "$spec_expected" ]]; then
    echo "    PASS (matches run_stateless_guest exactly)"
    return 0
  else
    # Show coalesced diff ranges to make tracking regressions easy.
    python3 -c "
a = bytes.fromhex('$actual')
s = bytes.fromhex('$spec_expected')
diffs = [i for i in range(len(a)) if a[i] != s[i]]
ranges = []
cur = [diffs[0], diffs[0]]
for i in diffs[1:]:
    if i == cur[1] + 1:
        cur[1] = i
    else:
        ranges.append(tuple(cur)); cur = [i, i]
ranges.append(tuple(cur))
rs = ', '.join(f'[{lo}..{hi+1})' for lo, hi in ranges)
print(f'    spec diff: bytes {rs} differ from spec')
"
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
