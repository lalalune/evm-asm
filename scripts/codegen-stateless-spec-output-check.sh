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
  local witness_headers_hex="${10:-}"

  local safe="${label//[^0-9A-Za-z_]/_}"
  local input_file="$REPO_ROOT/gen-out/stateless_guest-spec-${safe}.input"
  local out_file="$REPO_ROOT/gen-out/stateless_guest-spec-${safe}.output"
  local spec_exp_file="$REPO_ROOT/gen-out/stateless_guest-spec-${safe}.spec-expected"
  local log_file="$REPO_ROOT/gen-out/stateless_guest-spec-${safe}.emu.log"

  echo "==> [$label] gen new-schema SSZ input + spec expected (chain_id=$cid, fork=$fork, code=${witness_code_hex:-empty}, state=${witness_state_hex:-empty}, pk=${public_key_hex:-empty}, bn=${block_number:-empty}, ts=${timestamp:-empty}, blob=${blob_schedule:-empty}, hdr=${witness_headers_hex:-empty})"
  uv run --directory execution-specs --quiet python3 "$REPO_ROOT/scripts/codegen-stateless-gen-fixture.py" "$cid" "$input_file" "$spec_exp_file" "$fork" "$witness_code_hex" "$witness_state_hex" "$public_key_hex" "$block_number" "$timestamp" "$blob_schedule" "$witness_headers_hex"

  # Guard against silent fail: if the spec generator crashed
  # (Python syntax error in the heredoc, missing import, etc.)
  # both $spec_exp_file and $out_file would be missing or empty,
  # and the later "actual == spec_expected" string compare would
  # see "" == "" and report PASS. Bail out loudly here instead.
  if [[ ! -s "$spec_exp_file" ]]; then
    echo "    FAIL: spec-expected file is missing or empty -- spec generator crashed" >&2
    return 1
  fi

  echo "==> [$label] ziskemu run"
  "$ZISKEMU" -e gen-out/stateless_guest.elf -i "$input_file" \
    -o "$out_file" -n 500000 >"$log_file" 2>&1

  if [[ ! -s "$out_file" ]]; then
    echo "    FAIL: ziskemu output file is missing or empty -- emulator crashed" >&2
    sed -n '$p' "$log_file" >&2 || true
    return 1
  fi

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

# Sepolia testnet chain_id (11155111 = 0xAA36A7). Variety
# dimension: a real-world public chain identifier with three
# distinct non-zero low bytes (a7, 36, aa) and all-zero high
# 5 bytes. Tests the encoder's two-SD chain_id split at
# OUTPUT[37..40) (low 3 = a7 36 aa) and OUTPUT[40..45) (high 5
# = 00 00 00 00 00) -- the seam at byte 39<->40 holds the
# topmost non-zero chain_id byte.
run_fixture "chain_sepolia"         11155111                || fail=1

# Sepolia (11155111) running Amsterdam fork. Combines the
# real-world chain_id seam-byte pattern from chain_sepolia
# (low 3 bytes a7 36 aa straddling the chain_id SD seam)
# with the real-world fork config from
# chain1_fork4_amsterdam_active (fork=4 + activation.bn=[0]
# + Amsterdam blob_schedule). Variety dimension: realistic
# chain_id + realistic fork config simultaneously. The
# encoder echoes a max-shape SszForkConfig under a non-trivial
# chain_id, exercising both the two-SD chain_id pack
# (OUTPUT[37..45)) and the bounded byte-copy of
# active_fork[16..L) on the same fixture for the first time.
# Spec: validate_chain_config succeeds (Sepolia chain_id
# isn't checked against any specific value), then
# validate_headers([]) -> IndexError -> False.
run_fixture "chain_sepolia_amsterdam" 11155111         4    ""           ""                  ""    "0"          ""           "14:21:11684671" || fail=1

# Edge: chain_id = 2^32 = 0x100000000. LE bytes
# 00 00 00 00 01 00 00 00. The encoder's chain_id split
# places the LOW 3 bytes at OUTPUT[37..40) and the HIGH 5 at
# OUTPUT[40..45). With 2^32, low 3 = 00 00 00 (zeros), high 5
# = 00 01 00 00 00 -- the lone non-zero byte 0x01 sits at
# OUTPUT[41], exactly the SECOND byte of the second SD's
# region. Tests the encoder's SRLI .x10 24 + OR' .x5
# (= 0xc0000000000) packing when the chain_id has zero bytes
# in the low 24 bits and a non-zero byte at exactly bit
# position 32..40 (i.e. shifted into the lowest byte of x7
# after SRLI 24).
run_fixture "chain_2pow32"          0x100000000             || fail=1

# Non-zero fork fixture -- exercises active_fork.fork passthrough.
# One fixture suffices: the encoder pipes the raw u64 from x12 to
# OUTPUT[49..57) without inspecting its value.
run_fixture "chain1_fork1"          1                  1    || fail=1

# Max valid ProtocolFork value -- amsterdam's ProtocolFork enum
# has 5 entries (0..4). Only fork=1 was previously tested; this
# adds the upper-bound case. The encoder writes the raw u64 at
# OUTPUT[49..57) without inspecting its value; spec's
# _ssz_to_fork_config maps the u64 to ProtocolFork(4).
run_fixture "chain1_fork4"          1                  4    || fail=1

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

# Edge: block_number = [0] -- the VALUE zero in a non-empty
# SszOptionalForkActivationValue list. SSZ treats this
# distinctly from the empty-list case: 8 bytes of u64 zero
# vs zero bytes. The encoder's byte-copy must write the
# explicit zero u64 at OUTPUT[73..81), NOT skip those bytes.
# Spec emits 81 bytes (same length as chain1_actbn) but
# with the bn slot all zeros. Tests that the encoder doesn't
# conflate "empty list" with "list containing zero".
run_fixture "chain1_actbn_zero"     1                  0    ""           ""                  ""    "0" || fail=1

# Variety: max ProtocolFork (4) + non-empty block_number.
# Cross-product not yet covered: fork-passthrough exercises
# at the upper enum bound (PR #6996) AND the variable-length
# encoder bn-passthrough (PR #6793) AT THE SAME TIME.
# Spec emits 81 bytes with fork=4 in OUTPUT[49..57) and the
# bn value in OUTPUT[73..81).
run_fixture "chain1_fork4_actbn"    1                  4    ""           ""                  ""    "999999999" || fail=1

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

# Cross-product: public_keys + both activation slots
# (block_number + timestamp). Largest output for fixtures that
# don't also drive blob_schedule -- 89 bytes -- with PK padding
# for ziskemu input-region headroom (see the [[ziskemu-input-
# slack]] memory note). Exercises the encoder's full
# active_fork[16..40) byte-copy path together with PK
# byte-budget shift.
run_fixture "chain1_pk_act_both"    1                  0    ""           ""                  "04$(printf '%064d' 0)$(printf '%064d' 0)"    "7777777777" "8888888888" || fail=1

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

# Realistic mainnet-amsterdam blob_schedule values (vs the
# arbitrary 100:200:300 in chain1_blob). target=14, max=21,
# base_fee_update_fraction=11,684,671 are amsterdam's actual
# constants (GasCosts.BLOB_SCHEDULE_TARGET/MAX/
# BLOB_BASE_FEE_UPDATE_FRACTION in execution-specs's amsterdam
# fork). Tests that the encoder handles realistic u64 values
# (including base_fee_update_fraction = 0xb24d7f, multi-byte)
# byte-for-byte against the spec.
run_fixture "chain1_blob_realistic" 1                  0    ""           ""                  ""    ""           ""           "14:21:11684671" || fail=1

# First fixture where spec's validate_chain_config() reaches
# the SUCCESS branch (returns active_fork) rather than
# raising an exception. Configuration:
#   chain_id = 1 (mainnet)
#   fork     = 4 (ProtocolFork.Amsterdam, the latest enum)
#   activation.block_number = [0] (set, so _is_activation_active
#     finds activation.block_number is not None; checking
#     execution_payload.block_number (0) < 0 is False --
#     activation is active for the empty execution_payload)
#   blob_schedule = (14, 21, 11684671)
#     -- exactly _expected_amsterdam_blob_schedule()
#        (BLOB_SCHEDULE_TARGET, BLOB_SCHEDULE_MAX,
#         BLOB_BASE_FEE_UPDATE_FRACTION in
#         execution-specs/amsterdam/vm/gas.py)
# Spec walks all three validate_chain_config checks
# successfully, then falls into validate_headers([]) which
# raises IndexError -- caught at the verify_stateless_new_payload
# level, successful_validation=False. Output: empty_npr_root
# + valid=False + chain_config echo.
# Variety dimension: SPEC code path that PASSES
# validate_chain_config. Until this fixture, every fixture's
# spec ran into UnsupportedForkConfigError /
# InactiveForkConfigError / InvalidForkActivationError. This
# fixture exercises the success-path arm of every check inside
# validate_chain_config.
run_fixture "chain1_fork4_amsterdam_active" 1          4    ""           ""                  ""    "0"          ""           "14:21:11684671" || fail=1

# Spec InactiveForkConfigError path. Identical to the
# fork=4 + Amsterdam-blob fixture except activation.bn=[1]
# (instead of [0]). _is_activation_active gets:
#   activation.block_number = Uint(1) (not None)
#   execution_payload.block_number = 0 (empty default)
#   0 < 1 -> True -> returns False -> spec raises
#   InactiveForkConfigError. The exception is caught at
#   verify_stateless_new_payload, successful_validation=False.
# Variety dimension: SPEC code path = InactiveForkConfigError
# inside validate_chain_config. Until this fixture, every
# fork=4 + Amsterdam-blob input hit
# _is_activation_active's success branch (bn=[0] passes the
# 0 < 0 check). This fixture exercises the False return.
run_fixture "chain1_fork4_inactive_bn" 1               4    ""           ""                  ""    "1"          ""           "14:21:11684671" || fail=1

# Spec "Witness headers are not contiguous" path.
# Configuration:
#   chain_id        = 1
#   fork            = 4 (Amsterdam -- passes validate_chain_config)
#   activation.bn   = [0]
#   blob_schedule   = (14, 21, 11684671)  [amsterdam expected]
#   witness.headers = VALID_TWO
#     (N=2 NON-chained -- h0.parent_hash=zero, h1.parent_hash=
#      zero; the parent_hash chain through keccak256(rlp(h0))
#      is broken because h1.parent_hash != keccak(h0))
# Spec flow:
#   validate_chain_config(...) -> SUCCESS
#   validate_headers([h0, h1]):
#     decode h0, h1 (RLP OK)
#     block_hashes = [keccak(h0), keccak(h1)]
#     for i=1: headers[1].parent_hash (= zero) !=
#              block_hashes[0] (= keccak(h0))
#     -> raises Exception("Witness headers are not contiguous")
#   caught at verify_stateless_new_payload -> False.
# Variety dimension: spec error path
# "Witness headers are not contiguous" -- distinct from the
# validate_chain_config errors and from the empty-headers
# IndexError. All prior fork=4 + Amsterdam fixtures either
# had empty headers (IndexError) or chained headers (success).
# This is the first fixture exercising the contiguity-failure
# branch of validate_headers.
run_fixture "chain1_fork4_noncontig"   1               4    ""           ""                  ""    "0"          ""           "14:21:11684671" "VALID_TWO" || fail=1

# UnsupportedForkConfigError via blob_schedule mismatch.
# Configuration:
#   chain_id      = 1
#   fork          = 4 (Amsterdam -- passes the fork check)
#   activation.bn = [0] (passes _is_activation_active)
#   blob_schedule = (15, 21, 11684671)  <-- target off by 1
#                                           (Amsterdam expects 14)
# Spec flow:
#   _is_activation_active(...)      -> True
#   active_fork.fork == Amsterdam   -> True
#   blob_schedule != amsterdam exp  -> raises
#     UnsupportedForkConfigError("...blob_schedule does not
#     match Amsterdam"). Caught -> successful_validation=False.
# Distinct sub-branch of UnsupportedForkConfigError. The
# OTHER UnsupportedForkConfigError ("Amsterdam stateless guest
# cannot execute X") is exercised by every fork=0/1 fixture;
# the blob-mismatch sub-branch was uncovered until now.
run_fixture "chain1_fork4_wrong_blob"  1               4    ""           ""                  ""    "0"          ""           "15:21:11684671" || fail=1

# fork=4 Amsterdam + activation.bn=[0] + Amsterdam blob +
# VALID_REALISTIC header (N=1, every K-PR-ignored field
# populated with realistic non-zero bytes). Cross-product of
# variety dimensions:
#   * spec walks past validate_chain_config success (#7067)
#   * spec walks past validate_headers success at N=1 (new)
#   * spec uses _decode_header's PRIMARY amsterdam branch
#     (distinct from PR #7075's PreviousForkHeader fallback)
#   * ASM K-PR pipeline parses a REALISTIC-shape RLP header
#     (with 32-byte non-zero parent_hash, coinbase, state_root,
#      etc.) and all K-PRs accept -> .Lsg_all_pass
# Previous fork=4 chained fixtures (PR #7068) used VALID_THREE
# headers with minimal-field cohorts; this is the first
# realistic-field-cohort fixture that the spec actually
# walks past validate_headers.
run_fixture "chain1_fork4_realistic_header" 1          4    ""           ""                  ""    "0"          ""           "14:21:11684671" "VALID_REALISTIC" || fail=1

# Spec rlp.DecodingError path inside validate_headers.
# Configuration:
#   chain_id        = 1
#   fork            = 4 (Amsterdam, passes validate_chain_config)
#   activation.bn   = [0]
#   blob_schedule   = (14, 21, 11684671)  [amsterdam expected]
#   witness.headers = single 32-byte 0xAA blob (not RLP-valid)
# Spec flow:
#   validate_chain_config(...) -> SUCCESS
#   validate_headers([0xAA * 32]):
#     _decode_header tries rlp.decode_to(Header, ...) -> fails
#       (the blob doesn't have the Header RLP shape)
#     tries rlp.decode_to(PreviousForkHeader, ...) -> also fails
#     -> raises rlp.DecodingError
#   caught at verify_stateless_new_payload -> False.
# Variety dimension: spec error path = rlp.DecodingError
# inside _decode_header (validate_headers's RLP-parse step).
# Distinct from the "not contiguous" path (PR #7071) which
# exercises VALID RLP that fails parent_hash linkage, and
# from the IndexError path (empty headers).
run_fixture "chain1_fork4_bad_rlp_header" 1            4    ""           ""                  ""    "0"          ""           "14:21:11684671" "$(printf 'aa%.0s' {1..32})" || fail=1

# Valid post-merge header with REALISTIC non-zero values for
# every K-PR-IGNORED field (parent_hash, coinbase, state_root,
# transactions_root, receipt_root, bloom, prev_randao,
# base_fee_per_gas, withdrawals_root, excess_blob_gas,
# parent_beacon_block_root, requests_hash, block_access_list_hash,
# slot_number). K-PR-CHECKED fields (difficulty, ommers_hash,
# nonce, extra_data length, gas_used/limit, blob_gas_used) stay
# at their valid post-merge values. Verifies K-PRs correctly
# IGNORE the unchecked fields rather than requiring them at
# zero defaults. Reaches .Lsg_all_pass.
run_fixture "chain1_valid_realistic" 1                 0    ""           ""                  ""    ""           ""           ""    "VALID_REALISTIC" || fail=1

# Cross-product boundary fixture: all four numeric-bound K-PR
# validators at their ACCEPT boundary simultaneously.
#   * K291 extra_data length = 32        (== max)
#   * K240 gas_used = 1000000            (== gas_limit)
#   * K278 blob_gas_used = 786432        (== 6*131072, exact multiple)
#   * K277 blob_gas_used = 786432        (== MAX_BLOB_GAS_PER_BLOCK)
# If any K-PR had a subtle off-by-one in its <= vs <
# comparator, the spec mismatch would surface here.
# Reaches .Lsg_all_pass.
run_fixture "chain1_valid_all_boundary" 1             0    ""           ""                  ""    ""           ""           ""    "VALID_ALL_BOUNDARY" || fail=1

# Triple cross-product: witness.codes + public_keys + block_number.
# witness.codes shifts chain_config_addr forward, block_number
# drives the variable-length encoder, and public_keys padding
# pushes mem_end far enough past chain_config_end that the
# encoder's trailing LBU reads stay in-bounds (see the [[ziskemu-
# input-slack]] memory note). Without the PK padding this exact
# witcode + actbn combo would panic ziskemu with "section not
# found"; the PK trick recovers it.
run_fixture "chain1_witcode_pk_actbn" 1                0    "deadbeef"   ""                  "04$(printf '%064d' 0)$(printf '%064d' 0)"    "1234567890" || fail=1
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

# Previously-blocked cross-product witness.codes + block_number
# (no PK padding), now passing thanks to the bounded byte-copy.
# Without the bound, this combo's mem slack between
# chain_config_end and ziskemu's input-region boundary is 0
# bytes, so the prior unrolled LBUs at chain_config + 28..76
# panicked with "section not found". The bounded loop stops at
# chain_config_end, never reaching the unmapped page.
run_fixture "chain1_witcode_actbn_unbounded" 1   0    "deadbeef"   ""                  ""    "1234567890" || fail=1

# Stronger stress for the bounded byte-copy: BOTH witness
# fields populated AND non-empty block_number, no PK padding.
# Under the old unrolled encoder, chain_config_end lands close
# enough to ziskemu's input-region boundary that the trailing
# unconditional LBUs at chain_config + 28..76 panic with
# "section not found". The bounded loop in PR #6843 stops at
# chain_config_end so the combination passes.
run_fixture "chain1_witboth_actbn_unbounded" 1   0    "deadbeef"   "a1b2c3d4e5f60718"  ""    "1234567890" || fail=1

# Non-empty witness.headers -- exercises the THIRD inner witness
# field, which the decoder's `decode_header_count` stub leaves
# inert (x16 = 0) so the validator pipeline takes the N=0 fast
# path. Spec's `validate_headers([bogus])` raises -> valid=False,
# matching the ELF's x11=0 stub. Adding a 32-byte arbitrary
# header tests that the decoder's outer-offset chase is robust
# even when witness.headers is non-empty.
run_fixture "chain1_witheaders"     1                  0    ""           ""                  ""    ""           ""           ""    "$(printf 'aa%.0s' {1..32})" || fail=1

# Two witness.headers entries -- exercises the SSZ list inner
# offset table (2 u32 offsets prefix the headers section)
# parallel to chain1_witcode_2 / chain1_witstate_2. The decoder
# still leaves x16=0 from the stub so the validator pipeline
# takes the N=0 fast path; ELF output stays the 73-byte
# valid=False template. Stress test for the bounded byte-copy
# under maximum-witness-headers byte-budget.
run_fixture "chain1_witheaders_2"   1                  0    ""           ""                  ""    ""           ""           ""    "$(printf 'aa%.0s' {1..32}):$(printf 'bb%.0s' {1..32})" || fail=1

# Three witness.headers entries -- exercises the validator
# pipeline's `.Lsg_bl` loop building sg_header_lengths for
# N=3, and the K-PR iteration over 3 headers. Since the
# decoder is now real (PR #6878), this fixture activates the
# pipeline with s2=3; the lengths loop runs 3 times, then the
# first validator (chain_validate_post_merge_full) fails RLP
# parse on the first bogus header and falls through to
# .Lsg_hash. Spec returns valid=False with chain_config echo;
# ELF matches.
run_fixture "chain1_witheaders_3"   1                  0    ""           ""                  ""    ""           ""           ""    "$(printf 'aa%.0s' {1..32}):$(printf 'bb%.0s' {1..32}):$(printf 'cc%.0s' {1..32})" || fail=1

# Single VALID post-merge header -- exercises the ALL-PASS
# branch of the validator pipeline for the first time. With
# the real `decode_header_count` from PR #6878, this fixture
# activates the pipeline at N=1; the K-PR validators each
# parse the RLP-encoded header (637 bytes) and pass:
#   - difficulty=0, ommers_hash=EMPTY, nonce=8 zeros (K290)
#   - extra_data length 0 (K291)
#   - gas_used 0 <= gas_limit 1000000 (K240)
#   - blob_gas_used 0, multiple of GAS_PER_BLOB and below MAX (K278/K277)
#   - timestamp/number checks vacuous at N=1 (K229/K230)
# Pipeline reaches `.Lsg_all_pass` -> `.Lsg_hash` -> halt.
# Spec runs validate_headers -> succeeds -> proceeds to STF
# with empty NPR -> exception -> valid=False. Output matches
# byte-for-byte at 73 bytes (chain_config echo + empty NPR
# root, both implementations write valid=False here).
run_fixture "chain1_valid_header"   1                  0    ""           ""                  ""    ""           ""           ""    "VALID_POST_MERGE" || fail=1

# Header that fails K290 (chain_validate_post_merge_full).
# Same shape as chain1_valid_header but difficulty=1 instead
# of 0. K290 checks the post-merge invariant difficulty==0;
# this fixture exercises the `.Lsg_fail_pm` path through the
# pipeline (vs `.Lsg_fail_rlp` exercised by the bogus
# witheaders fixtures). With #6878's pipeline mod, the path
# falls through to .Lsg_hash -> 73-byte valid=False output.
# Spec catches the validator exception and returns the same
# byte sequence. Match confirms K290 is actually triggered
# AND the .Lsg_fail_pm routing reaches the cleanup path.
run_fixture "chain1_invalid_diff"   1                  0    ""           ""                  ""    ""           ""           ""    "INVALID_DIFF" || fail=1

# Header that fails K291 (chain_validate_extra_data_length).
# Same shape as chain1_valid_header but extra_data has 33
# bytes instead of 0 -- exceeds the 32-byte amsterdam limit.
# Pipeline flow:
#   1. K290 passes (difficulty=0, ommers_hash=EMPTY, nonce=0).
#   2. K291 reads extra_data length, finds 33 > 32, sets
#      sg_kpr_valid=0, returns.
#   3. Pipeline branches to .Lsg_fail_ed -> .Lsg_unimpl
#      (= j .Lsg_hash, per PR #6878) -> halt.
# Output 73 bytes valid=False. Spec catches and returns same.
# Third validator-specific REJECT path exercised (after
# .Lsg_fail_rlp and .Lsg_fail_pm).
run_fixture "chain1_invalid_extra"  1                  0    ""           ""                  ""    ""           ""           ""    "INVALID_EXTRA" || fail=1

# Header that fails K240 (chain_validate_gas_used_under_limit).
# Valid post-merge shape except gas_used=1,000,001 exceeds
# gas_limit=1,000,000 by 1. K240 rejects.
# Pipeline: K290+K291 pass, K240 fails -> .Lsg_fail_gas ->
# .Lsg_unimpl (= j .Lsg_hash, post #6878) -> halt. Output 73
# bytes valid=False; spec catches and returns same.
run_fixture "chain1_invalid_gas"    1                  0    ""           ""                  ""    ""           ""           ""    "INVALID_GAS" || fail=1

# Header that fails K278 (chain_validate_blob_gas_used_multiple).
# Valid post-merge shape except blob_gas_used=1 -- not a
# multiple of GAS_PER_BLOB=131072. K278 rejects.
# Pipeline: K290+K291+K240 pass, K278 fails -> .Lsg_fail_bgm
# -> .Lsg_unimpl (= j .Lsg_hash, post #6878) -> halt.
# Output 73 bytes valid=False; spec catches and returns same.
run_fixture "chain1_invalid_blob_misalign" 1   0    ""           ""                  ""    ""           ""           ""    "INVALID_BLOB_MISALIGN" || fail=1

# Header that fails K277 (chain_validate_blob_gas_used_under_max).
# blob_gas_used=917504 = 7*131072: passes K278's multiple-of-
# GAS_PER_BLOB check, but exceeds MAX_BLOB_GAS_PER_BLOCK
# (6*131072 = 786432). K277 rejects.
# Pipeline: K290+K291+K240+K278 pass, K277 fails ->
# .Lsg_fail_bgum -> .Lsg_unimpl (= j .Lsg_hash, post #6878).
# Output 73 bytes valid=False; spec catches and returns same.
run_fixture "chain1_invalid_blob_overmax"  1   0    ""           ""                  ""    ""           ""           ""    "INVALID_BLOB_OVERMAX" || fail=1

# Two valid post-merge headers but the second's timestamp is
# not strictly greater than the first's (both 1234). K229
# (chain_validate_increasing_timestamps) rejects. The first
# multi-header REJECT path exercised.
# Pipeline: K290 / K291 / K240 / K278 / K277 each pass on
# both headers; K229 catches non-increasing -> .Lsg_fail_ts
# -> .Lsg_unimpl (= j .Lsg_hash, post #6878). Spec's
# validate_headers raises on contiguity (parent_hash is zero,
# does not chain to first header's keccak); both return
# 73 bytes valid=False.
run_fixture "chain1_invalid_ts"     1                  0    ""           ""                  ""    ""           ""           ""    "INVALID_TS" || fail=1

# Two valid post-merge headers with strictly increasing
# timestamps (so K229 passes) but non-consecutive numbers
# (1 and 3, not 1 and 2). K230 (chain_validate_consecutive_
# numbers) rejects. This completes the validator-pipeline
# REJECT-path coverage: all 7 K-PRs' individual reject
# paths plus .Lsg_fail_rlp now have at least one fixture.
# Pipeline flow:
#   1. .Lsg_bl builds sg_header_lengths[N=2].
#   2. K-PRs 290/291/240/278/277 each pass on both headers.
#   3. K229 passes (1234 < 2000).
#   4. K230 catches header[1].number != header[0].number + 1
#      (3 != 2), sets sg_kpr_valid=0.
#   5. Pipeline branches to .Lsg_fail_nm -> .Lsg_unimpl
#      (= j .Lsg_hash, post #6878).
run_fixture "chain1_invalid_nm"     1                  0    ""           ""                  ""    ""           ""           ""    "INVALID_NM" || fail=1

# Two valid post-merge headers with strictly increasing
# timestamps AND consecutive numbers. ALL 7 K-PR validators
# accept; the pipeline reaches .Lsg_all_pass for N=2 (the
# multi-header all-pass branch -- chain1_valid_header
# already covered N=1 all-pass in PR #6886). K229 and K230
# fire and ACCEPT for the first time in a passing fixture;
# previously they only had REJECT-path tests (#6905, #6908).
run_fixture "chain1_valid_two"      1                  0    ""           ""                  ""    ""           ""           ""    "VALID_TWO" || fail=1

# Boundary-accept test for K291. Header has extra_data of
# EXACTLY 32 bytes (the maximum allowed by K291). Pairs with
# chain1_invalid_extra (#6893, 33 bytes -> reject) to verify
# the boundary condition is on the right side. Pipeline
# reaches .Lsg_all_pass; output 73 bytes valid=False; spec
# matches via STF failure on empty NPR.
run_fixture "chain1_extra_at_boundary" 1   0    ""           ""                  ""    ""           ""           ""    "VALID_EXTRA_BOUNDARY" || fail=1

# Boundary-accept test for K240. Header has gas_used == gas_limit
# (1,000,000 == 1,000,000), the upper boundary of K240's
# gas_used <= gas_limit check. Pairs with chain1_invalid_gas
# (#6897, gas_used=1,000,001 > gas_limit -> reject) to verify
# the boundary is on the correct side: K240 accepts equality.
run_fixture "chain1_gas_at_boundary" 1    0    ""           ""                  ""    ""           ""           ""    "VALID_GAS_BOUNDARY" || fail=1

# Boundary-accept test for K278. Header has blob_gas_used =
# GAS_PER_BLOB (131072), an exact multiple of GAS_PER_BLOB
# AND <= MAX_BLOB_GAS_PER_BLOCK. K278 (multiple check)
# accepts; K277 (under-max check) also accepts.
# Pairs with chain1_invalid_blob_misalign (#6899, value=1 not
# a multiple -> reject) to verify the K278 boundary is on
# the correct side: K278 accepts a non-zero exact multiple.
run_fixture "chain1_blob_at_boundary" 1   0    ""           ""                  ""    ""           ""           ""    "VALID_BLOB_BOUNDARY" || fail=1

# Boundary-accept test for K277. Header has blob_gas_used =
# 6 * GAS_PER_BLOB = 786432 = MAX_BLOB_GAS_PER_BLOCK exactly.
# K278 accepts (exact multiple of 131072); K277 accepts (==
# max, not strictly less). Pairs with chain1_invalid_blob_
# overmax (#6901, value = 7*131072 > max -> reject).
#
# Completes the accept/reject boundary coverage for all four
# numeric-bound K-PR validators:
#   K291: 32 (accept,  #6916) / 33 (reject, #6893)
#   K240: == (accept,  #6920) / +1 (reject, #6897)
#   K278:  131072 (accept, #6923) / 1 (reject, #6899)
#   K277: 786432 (accept, this PR) / 917504 (reject, #6901)
run_fixture "chain1_blob_max_at_boundary" 1 0  ""           ""                  ""    ""           ""           ""    "VALID_BLOB_MAX_BOUNDARY" || fail=1

# K290 sub-check: header has difficulty=0, ommers_hash=EMPTY,
# but nonce != b'\\x00' * 8. K290 (chain_validate_post_merge_
# full) rejects on the nonce check (vs the difficulty check
# tested by chain1_invalid_diff #6889). Verifies K290
# enforces ALL its post-merge invariants, not just difficulty.
# Output 73 bytes valid=False; spec catches and returns same.
run_fixture "chain1_invalid_nonce"  1                  0    ""           ""                  ""    ""           ""           ""    "INVALID_NONCE" || fail=1

# K290 third sub-check: header with difficulty=0, nonce=zeros,
# but ommers_hash != EMPTY_OMMER_HASH (all 0xff bytes). K290
# rejects via the ommers_hash check. Completes K290's three
# post-merge invariant sub-checks:
#   - difficulty=0       (chain1_invalid_diff, #6889)
#   - nonce=zeros        (chain1_invalid_nonce, #6933)
#   - ommers_hash=EMPTY  (this PR)
# Same fail label (.Lsg_fail_pm) reached via the third
# in-K-PR code path.
run_fixture "chain1_invalid_ommers" 1                  0    ""           ""                  ""    ""           ""           ""    "INVALID_OMMERS" || fail=1

# Regression guard for K240's unsigned (BGTU) comparison.
# Single header with gas_used = 2^63 - 1 = 0x7FFFFFFFFFFFFFFF
# (max positive i64) and gas_limit = 2^63 = 0x8000000000000000
# (INT64_MIN if interpreted signed).
# Unsigned: gas_used < gas_limit -> K240 BGTU accepts.
# Signed:   gas_used > gas_limit -> a buggy BGT swap rejects.
# Today both paths land at valid=False via .Lsg_hash so the
# output is byte-identical, but this fixture locks in the
# unsigned-ness of the gas comparator before the REASON
# surface is reintroduced -- sister to chain1_valid_ts_hibit
# for the K229 timestamp comparator.
run_fixture "chain1_valid_gas_hibit" 1                 0    ""           ""                  ""    ""           ""           ""    "VALID_GAS_HIBIT" || fail=1

# Two headers: first valid, second has difficulty=1. K290
# (chain_validate_post_merge_full) iterates: first header
# passes, SECOND fails. Verifies the per-header iteration
# loop body actually checks every header (not just the first).
# Same fail label (.Lsg_fail_pm) as chain1_invalid_diff but
# reached on the second loop iteration rather than the first.
run_fixture "chain1_invalid_diff_at_1" 1               0    ""           ""                  ""    ""           ""           ""    "INVALID_DIFF_AT_1" || fail=1

# Two headers: first valid (gas_used=0 <= gas_limit=1e6),
# second has gas_used > gas_limit. K290 and K291 iterate
# 2 times each (both pass on both headers); K240 iterates
# 2 times -- passes on header 0 (0 <= 1e6), FAILS on
# header 1 (1000001 > 1000000). Closes the K240 iteration
# coverage gap: existing INVALID_DIFF_AT_1 covers K290's
# per-header loop body at the LAST index, and
# INVALID_EXTRA_AT_2 covers K291's, but K240's per-header
# iteration was only ever exercised at index 0 via
# INVALID_GAS. This fixture exercises K240's loop body
# beyond the first iteration.
run_fixture "chain1_invalid_gas_at_1"  1               0    ""           ""                  ""    ""           ""           ""    "INVALID_GAS_AT_1" || fail=1

# Two headers: first valid (blob_gas_used=0), second has
# blob_gas_used = 7 * 131072 = 917504. The value is a
# multiple of GAS_PER_BLOB so K278 passes, but exceeds
# MAX_BLOB_GAS_PER_BLOCK = 6 * 131072 = 786432 so K277
# rejects. K290 / K291 / K240 / K278 iterate twice (all
# pass); K277 iterates twice -- passes on header 0
# (0 <= 786432), FAILS on header 1 (917504 > 786432).
# Closes the K277 iteration coverage gap and (together with
# the sister K240/K278 AT_1 fixtures) completes the per-K-PR
# iteration matrix at the non-zero index.
run_fixture "chain1_invalid_blob_overmax_at_1" 1       0    ""           ""                  ""    ""           ""           ""    "INVALID_BLOB_OVERMAX_AT_1" || fail=1

# Two headers: first valid (blob_gas_used=0, trivially a
# multiple of GAS_PER_BLOB=131072), second has blob_gas_used=1
# (NOT a multiple). K290 / K291 / K240 iterate 2 times each
# (all pass); K278 iterates 2 times -- passes on header 0,
# FAILS on header 1. Closes the K278 iteration coverage gap.
# Sister to chain1_invalid_diff_at_1 (K290) /
# chain1_invalid_extra_at_2 (K291) / chain1_invalid_ts_at_2
# (K229) / chain1_invalid_nm_at_2 (K230) / etc. -- verifies
# K278's per-header loop body actually checks every header.
run_fixture "chain1_invalid_blob_misalign_at_1" 1      0    ""           ""                  ""    ""           ""           ""    "INVALID_BLOB_MISALIGN_AT_1" || fail=1

# Three headers: 0 and 1 valid, header[2] has extra_data
# length 33. K290 iterates 3 times (all pass); K291 iterates
# 3 times -- passes on 0 and 1, FAILS on 2. Tests K-PR
# iteration loop body at the LAST index in a multi-header
# pipeline, complementing chain1_invalid_diff_at_1 (fail at
# index 1 of 2) by checking failure detection at index 2 of 3.
run_fixture "chain1_invalid_extra_at_2" 1              0    ""           ""                  ""    ""           ""           ""    "INVALID_EXTRA_AT_2" || fail=1

# Three headers where K229 catches between header[1] and
# header[2] (timestamps 1234, 2000, 2000). The FIRST pair
# (0->1) passes strictly-increasing check, the SECOND pair
# (1->2) fails (2000 not strictly > 2000). Tests K229's
# per-pair loop body at the LAST pair index of an N=3 input,
# complementing chain1_invalid_ts (#6905, N=2, fail at pair 0)
# by checking fail-detection at the higher pair index.
run_fixture "chain1_invalid_ts_at_2"    1              0    ""           ""                  ""    ""           ""           ""    "INVALID_TS_AT_2" || fail=1

# Three headers where K230 catches at the SECOND pair. Numbers
# 1, 2, 4 -- pair (0, 1) is consecutive (2 == 1+1) but pair
# (1, 2) is NOT (4 != 2+1). Timestamps strictly increasing
# so K229 passes. Tests K230's per-pair loop body at the LAST
# pair index, complementing chain1_invalid_nm (#6908, N=2
# fail at pair 0).
run_fixture "chain1_invalid_nm_at_2"    1              0    ""           ""                  ""    ""           ""           ""    "INVALID_NM_AT_2" || fail=1

# Three chained valid post-merge headers. parent_hash chain
# computed via keccak256 so spec's validate_headers accepts
# (contiguity holds). All K-PRs accept (timestamps increasing
# 1234<2000<3000, numbers consecutive 1,2,3). ELF reaches
# .Lsg_all_pass for N=3 -- first N=3 all-pass exercise.
# Spec's validate_headers succeeds, then STF fails on empty
# NPR -> valid=False. ELF: valid=False from x11 stub. Match.
run_fixture "chain1_valid_three"    1                  0    ""           ""                  ""    ""           ""           ""    "VALID_THREE" || fail=1

# Deepest spec path so far -- BOTH validate_chain_config AND
# validate_headers reach their success branches:
#   chain_id      = 1
#   fork          = 4 (Amsterdam)
#   activation.bn = [0]
#   blob_schedule = (14, 21, 11684671)  [== amsterdam expected]
#   witness.headers = VALID_THREE
#     (3 chained valid post-merge headers, parent_hash linked
#      via keccak256(rlp(h_i)))
# Spec flow:
#   validate_chain_config(...) -> RETURNS active_fork
#   validate_headers([h0,h1,h2]) -> returns (decoded, hashes)
#                                   [contiguity OK]
#   parent_header = h2
#   chain_context, pre_state built
#   execute_new_payload_request(EMPTY_NPR, ...) -> raises
#     (execution_payload has zero block_hash etc.; doesn't
#      match the parent_hash chain we just built) -> caught
#     at verify_stateless_new_payload -> False.
# All earlier fixtures bailed at validate_chain_config OR
# validate_headers; this fixture is the first to drive the
# spec past both checks into execute_new_payload_request.
# Variety dimension: spec code path coverage at the deepest
# pre-execution layer.
run_fixture "chain1_fork4_valid_chain" 1               4    ""           ""                  ""    "0"          ""           "14:21:11684671" "VALID_THREE" || fail=1

# N=8 chained valid post-merge headers. Extends K-PR
# iteration depth past the previous N=3 ceiling:
#   K229 performs 7 strict-increase timestamp pair comparisons
#   K230 performs 7 parent_number + 1 == child_number checks
#   K290 / K291 / K240 / K278 / K277 each iterate over all 8
#   headers individually
# parent_hash linkage via keccak256(rlp(h_i)) so spec's
# validate_headers ALSO succeeds (contiguity holds);
# ~4600 bytes of witness.headers section. Catches latent
# off-by-one or loop-termination bugs that only surface
# beyond the small-N range of existing fixtures.
run_fixture "chain1_valid_eight"    1                  0    ""           ""                  ""    ""           ""           ""    "VALID_EIGHT" || fail=1

# N=2 chained valid post-merge headers, both with the full
# VALID_REALISTIC field cohort (every K-PR-ignored field
# populated with realistic non-zero bytes). parent_hash chain
# via keccak256(rlp(h0)) so spec's validate_headers also
# accepts contiguity. All K-PR validators accept; both reach
# .Lsg_all_pass. Cross-product of "realistic field cohort"
# (was only ever N=1) and "chained 2-header all-pass" (was
# only ever minimal-field cohort). Exercises the K-PR
# pipeline + spec's validate_headers + the realistic
# RLP-encoded header size (~600 bytes each, ~1200 bytes of
# witness.headers section) simultaneously.
run_fixture "chain1_valid_realistic_two" 1            0    ""           ""                  ""    ""           ""           ""    "VALID_REALISTIC_TWO" || fail=1

# Regression guard for K229's unsigned timestamp comparison.
# N=2 chained valid post-merge headers with timestamps that
# straddle the u64 sign-bit boundary:
#   ts[0] = 2^63 - 1 = 0x7FFFFFFFFFFFFFFF (max positive i64)
#   ts[1] = 2^63     = 0x8000000000000000 (INT64_MIN signed)
# Unsigned: ts[1] > ts[0] -> K229 accepts (uses BGEU). A
# buggy BGE swap would interpret ts[1] as a large negative,
# reject incorrectly, and -- once the K-PR pipeline surfaces
# REASON codes -- diverge from spec. Today both paths land at
# valid=False via the .Lsg_hash fall-through; the fixture
# locks in the unsigned-ness of the comparator before that
# surface is reintroduced.
run_fixture "chain1_valid_ts_hibit" 1                  0    ""           ""                  ""    ""           ""           ""    "VALID_TS_HIBIT" || fail=1

# Kitchen-sink fixture -- every input slot populated
# simultaneously. All three inner witness fields (state +
# codes + headers) carry one entry each; public_keys has one
# 65-byte entry; chain_config.active_fork has bn=[N] +
# ts=[T] + blob=[entry] = MAX active_fork (64 bytes). Spec
# emits 113 bytes (the maximum-shape SszForkConfig echo).
# Stress test for the bounded byte-copy under maximum input
# byte-budget (witness ~68 bytes + chain_config 76 bytes +
# pk 65 bytes + npr 596 bytes), validating that the
# decoder's outer-offset chase and the encoder's bounded
# loop work together at the upper end of every variable
# dimension simultaneously.
run_fixture "chain1_kitchen_sink"   1                  0    "deadbeef"   "a1b2c3d4e5f60718"  "04$(printf '%064d' 0)$(printf '%064d' 0)"    "5555555555" "6666666666" "1000:2000:3000"    "$(printf 'aa%.0s' {1..32})" || fail=1

# Kitchen-sink + real RLP-encoded VALID_POST_MERGE header.
# Identical input shape to chain1_kitchen_sink (every variable
# slot populated, max-shape SszForkConfig, full PK) but the
# witness.headers entry is a real RLP-encoded post-merge
# Header instead of 32 bytes of 0xAA. Drives the K-PR pipeline
# down the all-pass path (K290/K291/K240/K278/K277 all
# accept; K229/K230 vacuous at N=1) simultaneously with the
# encoder's bounded byte-copy + chain_id pack + chain_config
# echo paths. Previously the kitchen-sink fixture stopped at
# the first K-PR's RLP parse failure (status != 0 -> fall
# through to .Lsg_hash) so the validator bodies were never
# fully exercised under max-input conditions. This fixture
# closes that gap.
run_fixture "chain1_kitchen_real_header" 1            0    "deadbeef"   "a1b2c3d4e5f60718"  "04$(printf '%064d' 0)$(printf '%064d' 0)"    "5555555555" "6666666666" "1000:2000:3000"    "VALID_POST_MERGE" || fail=1

# All numeric slots at u64 max (0xFFFFFFFFFFFFFFFF). Tests
# the encoder's bit-packing and byte-copy under full-width
# values in every slot: chain_id, fork, block_number,
# timestamp, and all three blob_schedule u64s.
# fork=0xFFFFFFFFFFFFFFFF is out of the ProtocolFork enum
# range but the encoder doesn't inspect the value -- it
# just passes the raw u64 through (the SSZ-side conversion
# in spec also doesn't validate at decode time for this
# encoder-only test).
run_fixture "chain_max_all_max"     0xFFFFFFFFFFFFFFFF 0    ""           ""                  ""    "0xFFFFFFFFFFFFFFFF" "0xFFFFFFFFFFFFFFFF" "0xFFFFFFFFFFFFFFFF:0xFFFFFFFFFFFFFFFF:0xFFFFFFFFFFFFFFFF" || fail=1

# Absolute extreme: kitchen-sink + max-values combined.
# Every input slot is populated AND every numeric value is at
# u64 max. Tests the encoder under simultaneous extremes:
# maximum-shape SszForkConfig (113-byte output), maximum
# byte-budget for chain_config_offset shift (full witness +
# pk), and all-1 bits flowing through the bit-packed bytes
# [32..48) and the bounded byte-copy [49..113). If any path
# has a subtle bug with 0xFF bytes under input-layout drift,
# this fixture catches it.
run_fixture "chain_extreme"         0xFFFFFFFFFFFFFFFF 0    "deadbeef"   "a1b2c3d4e5f60718"  "04$(printf '%064d' 0)$(printf '%064d' 0)"    "0xFFFFFFFFFFFFFFFF" "0xFFFFFFFFFFFFFFFF" "0xFFFFFFFFFFFFFFFF:0xFFFFFFFFFFFFFFFF:0xFFFFFFFFFFFFFFFF"    "$(printf 'aa%.0s' {1..32})" || fail=1

if [[ "$fail" -eq 0 ]]; then
  echo "==> PASS: all spec-output fixtures match the new SSZ schema"
  exit 0
else
  echo "==> FAIL: at least one fixture mismatched"
  exit 1
fi
