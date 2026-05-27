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
# max-u64) at the default fork=0; one fork=1 case
# (`chain1_fork1`) exercising the `active_fork.fork` passthrough
# from input through to OUTPUT[49..57); and one non-empty
# `witness.codes` case (`chain1_witcode`) exercising the decoder's
# outer-offset walk under input-layout drift.
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
  local fork="${3:-0}"
  local witness_code_hex="${4:-}"
  local witness_state_hex="${5:-}"
  local public_key_hex="${6:-}"
  local block_number="${7:-}"
  local timestamp="${8:-}"
  local blob_schedule="${9:-}"

  local safe="${label//[^0-9A-Za-z_]/_}"
  local input_file="$REPO_ROOT/gen-out/stateless_guest-spec-${safe}.input"
  local out_file="$REPO_ROOT/gen-out/stateless_guest-spec-${safe}.output"
  local spec_exp_file="$REPO_ROOT/gen-out/stateless_guest-spec-${safe}.spec-expected"
  local log_file="$REPO_ROOT/gen-out/stateless_guest-spec-${safe}.emu.log"

  echo "==> [$label] gen new-schema SSZ input + spec expected (chain_id=$cid, fork=$fork, code=${witness_code_hex:-empty}, state=${witness_state_hex:-empty}, pk=${public_key_hex:-empty}, bn=${block_number:-empty}, ts=${timestamp:-empty}, blob=${blob_schedule:-empty})"
  uv run --directory execution-specs --quiet python3 -c "
import struct, sys
from ethereum.forks.amsterdam.stateless_ssz import (
    MAX_BYTES_PER_CODE,
    MAX_BYTES_PER_WITNESS_NODE,
    MAX_PUBLIC_KEYS,
    MAX_WITNESS_CODES,
    MAX_WITNESS_NODES,
    PUBLIC_KEY_BYTES,
    STATELESS_INPUT_SCHEMA_ID_BYTES,
    SszBlobSchedule,
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
from remerkleable.byte_arrays import ByteList, ByteVector
from remerkleable.complex import List as SszList

cid = int(sys.argv[1], 0)
fork_idx = int(sys.argv[4], 0)
code_hex = sys.argv[5]
state_hex = sys.argv[6]
pk_hex = sys.argv[7]
bn_str = sys.argv[8]
ts_str = sys.argv[9]
blob_str = sys.argv[10]

# Build the new-schema StatelessInput: empty new_payload_request,
# witness whose 'state'/'codes' lists each hold zero or more
# entries (controlled by the fixture), 'headers' empty,
# chain_config(cid, SszForkConfig(fork=fork_idx, empty activation,
# empty blob_schedule)), empty public_keys.
bn_list = SszOptionalForkActivationValue()
if bn_str:
    bn_list = SszOptionalForkActivationValue(uint64(int(bn_str, 0)))
ts_list = SszOptionalForkActivationValue()
if ts_str:
    ts_list = SszOptionalForkActivationValue(uint64(int(ts_str, 0)))
activation = SszForkActivation(
    block_number=bn_list,
    timestamp=ts_list,
)
blob_sched = SszOptionalBlobSchedule()
if blob_str:
    parts = blob_str.split(':')
    assert len(parts) == 3, f'blob must be target:max:base_fee, got {blob_str!r}'
    entry = SszBlobSchedule(
        target=uint64(int(parts[0], 0)),
        max=uint64(int(parts[1], 0)),
        base_fee_update_fraction=uint64(int(parts[2], 0)),
    )
    blob_sched = SszOptionalBlobSchedule(entry)
fork_cfg = SszForkConfig(
    fork=uint64(fork_idx),
    activation=activation,
    blob_schedule=blob_sched,
)
cc = SszChainConfig(chain_id=uint64(cid), active_fork=fork_cfg)

CodeBL = ByteList[MAX_BYTES_PER_CODE]
CodesList = SszList[CodeBL, MAX_WITNESS_CODES]
codes_arg = ()
if code_hex:
    # Multiple entries separated by ':', each is a hex blob.
    code_entries = code_hex.split(':')
    codes_arg = tuple(CodeBL(bytes.fromhex(c)) for c in code_entries)

NodeBL = ByteList[MAX_BYTES_PER_WITNESS_NODE]
NodesList = SszList[NodeBL, MAX_WITNESS_NODES]
state_arg = ()
if state_hex:
    state_entries = state_hex.split(':')
    state_arg = tuple(NodeBL(bytes.fromhex(s)) for s in state_entries)

witness = SszExecutionWitness(
    state=NodesList(*state_arg),
    codes=CodesList(*codes_arg),
)

PkBV = ByteVector[PUBLIC_KEY_BYTES]
PkList = SszList[PkBV, MAX_PUBLIC_KEYS]
pk_args = ()
if pk_hex:
    pk_entries = pk_hex.split(':')
    pk_args = tuple(PkBV(bytes.fromhex(p)) for p in pk_entries)

ssz_input = SszStatelessInput(
    new_payload_request=SszNewPayloadRequest(),
    witness=witness,
    chain_config=cc,
    public_keys=PkList(*pk_args),
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
with open(sys.argv[3], 'w') as f:
    f.write(spec_bytes.hex())
" "$cid" "$input_file" "$spec_exp_file" "$fork" "$witness_code_hex" "$witness_state_hex" "$public_key_hex" "$block_number" "$timestamp" "$blob_schedule"

  echo "==> [$label] ziskemu run"
  "$ZISKEMU" -e gen-out/stateless_guest.elf -i "$input_file" \
    -o "$out_file" -n 500000 >"$log_file" 2>&1

  local actual spec_expected spec_len
  spec_expected="$(cat "$spec_exp_file")"
  spec_len=$(( ${#spec_expected} / 2 ))
  actual="$(xxd -p -l "$spec_len" "$out_file" | tr -d '\n')"

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
# Fork = 0 (default) fixtures -- exercise chain_id read.
run_fixture "chain1"                1                       || fail=1
run_fixture "chain_big"             0x1234567890ABCDEF      || fail=1
run_fixture "chain_zero"            0                       || fail=1
run_fixture "chain_max_u32"         0xFFFFFFFF              || fail=1
run_fixture "chain_max_u64"         0xFFFFFFFFFFFFFFFF      || fail=1

# Non-zero fork fixture -- exercises active_fork.fork passthrough.
# One fixture suffices: the encoder pipes the raw u64 from x12 to
# OUTPUT[49..57) without inspecting its value.
run_fixture "chain1_fork1"          1                  1    || fail=1

# Non-empty witness.codes -- exercises the decoder's outer-offset
# walk on a non-trivial input layout. The witness section grows by
# one ByteList entry; the outer `chain_config` offset (read by
# `read_chain_id` from SSZ_BASE+8) shifts accordingly. ELF output
# is unchanged (chain_config echoed, valid=False as for empty
# witness), so this verifies that `read_chain_id` /
# `read_active_fork` still land on the correct `chain_config_addr`
# under input-layout drift. Code blob is 4 deterministic bytes.
run_fixture "chain1_witcode"        1                  0    "deadbeef" || fail=1

# Same path with TWO witness.codes entries -- exercises the SSZ
# list-of-variable-size-elements encoding inside witness.codes (an
# inner u32 offset table prefixes the codes section). The outer
# `chain_config` offset shifts further than the single-entry case,
# and the decoder must still chase it correctly.
run_fixture "chain1_witcode_2"      1                  0    "deadbeef:cafef00d" || fail=1

# Non-empty witness.state -- parallel to witness.codes but exercises
# the FIRST inner field of `SszExecutionWitness` (state nodes). The
# inner offset table inside the witness section now has state_offset
# strictly less than codes_offset, but the outer-offset chase the
# decoder performs (SSZ_BASE+8 -> chain_config_addr) is identical:
# we verify the decoder doesn't accidentally depend on which inner
# witness field is non-empty. State entry is one arbitrary node.
run_fixture "chain1_witstate"       1                  0    ""           "a1b2c3d4e5f60718" || fail=1

# Two witness.state entries -- parallel to chain1_witcode_2 but on
# the FIRST inner witness field. The state list is variable-size
# elements (ByteList[MAX_BYTES_PER_WITNESS_NODE]), so a 2-element
# list ships its own u32 inner offset table prefix. Completes the
# 1-vs-2 entries matrix across all three list-type SSZ slots
# (codes, state, public_keys).
run_fixture "chain1_witstate_2"     1                  0    ""           "a1b2c3d4e5f60718:9988776655443322" || fail=1

# Both witness.state AND witness.codes non-empty simultaneously --
# the inner-witness offset table now has three pairwise-distinct
# offsets (state_offset < codes_offset < headers_offset), pushing
# the outer chain_config offset further than any single-field case.
# Decoder still chases SSZ_BASE+8 -> chain_config_addr correctly.
run_fixture "chain1_witboth"        1                  0    "deadbeef"   "a1b2c3d4e5f60718" || fail=1

# Non-empty public_keys -- exercises the FOURTH (last) outer field.
# public_keys is a list of fixed-size `ByteVector[PUBLIC_KEY_BYTES]`
# (65 bytes each) -- so no INNER offset table, just concatenated
# 65-byte elements. The outer offsets[3] (public_keys_offset, read
# from SSZ_BASE+12) is unchanged because the field comes AFTER
# chain_config; only the SSZ blob total length grows. The decoder
# reads SSZ_BASE+8 (offsets[2]) and never touches offsets[3], so
# the ELF output is unchanged. PK is 65 deterministic bytes
# (04 || 32 zeros || 32 zeros = SEC1 uncompressed-marker prefix).
run_fixture "chain1_pk"             1                  0    ""           ""                  "04$(printf '%064d' 0)$(printf '%064d' 0)" || fail=1

# Two public_keys entries -- exercises a 2-element SSZ list of
# fixed-size ByteVectors. Unlike SszList[ByteList, N] (variable-
# size elements, requires an inner offset table), this list has
# NO inner offset table; the 130-byte payload is just the two
# 65-byte entries concatenated. Doubles the public_keys
# byte-budget. Decoder's outer-offset chase is unaffected.
run_fixture "chain1_pk_2"           1                  0    ""           ""                  "04$(printf '%064d' 0)$(printf '%064d' 0):04$(printf '%064d' 1)$(printf '%064d' 1)" || fail=1

# All three non-chain_config outer slots populated simultaneously
# -- witness.state + witness.codes + public_keys -- the largest
# input-layout complexity that still keeps spec output unchanged
# (chain_config echoed, valid=False). Verifies the decoder's
# outer-offset read at SSZ_BASE+8 is robust under the maximum
# byte-budget shift this fixture set produces.
run_fixture "chain1_all_outer"      1                  0    "deadbeef"   "a1b2c3d4e5f60718"  "04$(printf '%064d' 0)$(printf '%064d' 0)" || fail=1

# Non-empty `active_fork.activation.block_number = [N]` --
# exercises the encoder's variable-length-output path. Spec
# emits 81 bytes (vs 73 for empty activation): the extra 8
# bytes are the block_number u64 at OUTPUT[73..81). The
# encoder now byte-copies active_fork[16..32) from input,
# which covers both the activation header (offset_block_number
# + offset_timestamp, bytes 16..24) and the block_number value
# (bytes 24..32) when present.
run_fixture "chain1_actbn"          1                  0    ""           ""                  ""    "1234567890" || fail=1

# Symmetric: non-empty `activation.timestamp = [N]`, block_number
# empty. Same active_fork size as the bn=[N] case (32 bytes), so
# spec is also 81 bytes -- but `offset_timestamp` stays at 8 (no
# block_number bytes in front) and OUTPUT[73..81) holds the
# timestamp u64 instead of the block_number u64. Validates that
# the encoder's byte-copy of active_fork[16..32) generalises
# correctly across the offset/body permutation.
run_fixture "chain1_actts"          1                  0    ""           ""                  ""    ""           "9876543210" || fail=1

# Both `block_number = [B]` AND `timestamp = [T]` non-empty.
# Activation body grows to 24 bytes (8 offsets + 8 bn + 8 ts);
# active_fork = 40 bytes; spec output = 89 bytes. The encoder
# now byte-copies active_fork[32..40) into OUTPUT[81..89) (the
# timestamp value slot), in addition to the [16..32) copy from
# #6793. offset_blob_schedule becomes 40 (= 0x28) -- still
# fits in 1 byte, so the LBU+SB at OUTPUT[61] handles it.
run_fixture "chain1_act_both"       1                  0    ""           ""                  ""    "1111111111" "2222222222" || fail=1

# Non-empty `blob_schedule = [SszBlobSchedule(...)]` with one
# fixed-size 24-byte entry (3 u64s: target, max,
# base_fee_update_fraction). Activation stays empty, so
# active_fork[16..24) is the empty-activation header and
# active_fork[24..48) is the blob_schedule entry. Spec emits
# 97 bytes = 73 (empty active_fork base) + 24 (blob_schedule).
# offset_blob_schedule remains 24 (= 16 + 8 empty activation).
# The encoder's byte-copy of active_fork[16..48) now covers
# all three u64s of the entry.
run_fixture "chain1_blob"           1                  0    ""           ""                  ""    ""           ""           "100:200:300" || fail=1

# Cross-product: non-empty public_keys AND non-empty
# blob_schedule. Both fields shift only `offsets[3]`
# (public_keys_offset) and the SSZ blob total length; neither
# affects chain_config_offset. The encoder's full byte-copy of
# active_fork[16..64) (covering the entire blob_schedule
# entry) must produce 97 bytes that match spec. PK padding
# gives plenty of mem slack so the byte-copy never reads past
# ziskemu's input section.
run_fixture "chain1_pk_blob"        1                  0    ""           ""                  "04$(printf '%064d' 0)$(printf '%064d' 0)"    ""           ""           "100:200:300" || fail=1
# Cross-product: non-empty public_keys AND non-empty
# block_number. The decoder's outer-offset chase
# (SSZ_BASE+8 -> chain_config_addr) must land correctly under
# input-layout drift, AND the encoder's variable-length byte-
# copy must produce the 81-byte block_number passthrough.
# public_keys (65 bytes) sits AFTER chain_config in the outer
# SSZ blob, so it doesn't shift chain_config_offset; it does
# extend the input file enough that the encoder's trailing
# byte-copy reads stay within ziskemu's mapped input region
# (cross-products with witness.codes/state would land 0..few
# bytes of mem slack -- too tight, would panic).
run_fixture "chain1_pk_actbn"       1                  0    ""           ""                  "04$(printf '%064d' 0)$(printf '%064d' 0)"    "1234567890" || fail=1
# Cross-product corner: bn=[B], ts=[T], blob=[entry] all
# populated simultaneously. MAX active_fork = 64 bytes (16
# fc-header + 24 activation body + 24 blob_schedule), so spec
# emits 113 bytes -- the largest spec output the new-schema
# SszForkConfig can produce. offset_blob_schedule = 40
# (= 0x28); still fits in 1 byte.
run_fixture "chain1_act_blob_all"   1                  0    ""           ""                  ""    "3333333333" "4444444444" "500:600:700" || fail=1

if [[ "$fail" -eq 0 ]]; then
  echo "==> PASS: all spec-output fixtures match the new SSZ schema"
  exit 0
else
  echo "==> FAIL: at least one fixture mismatched"
  exit 1
fi
