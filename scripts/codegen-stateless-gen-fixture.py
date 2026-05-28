#!/usr/bin/env python3
"""
codegen-stateless-gen-fixture.py -- generate one (input, spec-expected)
fixture pair for the new-schema run_stateless_guest round-trip test.

Driven by `scripts/codegen-stateless-spec-output-check.sh`. Pulled out of
that script's inline heredoc to make the fixture configuration tractable
and silently-failing edits less likely (#6951's blind-spot fix only
catches missing files, not Python edit errors).

CLI:
    python3 codegen-stateless-gen-fixture.py \
        <chain_id> <input_path> <spec_expected_path> <fork> \
        <witness_code_hex> <witness_state_hex> <public_key_hex> \
        <block_number> <timestamp> <blob_schedule> \
        <witness_headers_hex>

Each list-shaped hex argument may be empty (no entries) or contain ':'
separated hex blobs (one per entry). The blob_schedule arg is
target:max:base_fee_update_fraction (decimal/hex, one entry only).

The `witness_headers_hex` arg also supports special sentinels that build
RLP-encoded post-merge Header objects via `ethereum.forks.amsterdam.blocks`
(VALID_POST_MERGE / INVALID_DIFF / INVALID_EXTRA / INVALID_GAS /
INVALID_BLOB_MISALIGN / INVALID_BLOB_OVERMAX / VALID_EXTRA_BOUNDARY /
VALID_GAS_BOUNDARY / VALID_BLOB_BOUNDARY / VALID_BLOB_MAX_BOUNDARY /
INVALID_NONCE / INVALID_OMMERS / VALID_TWO / VALID_THREE / INVALID_TS /
INVALID_NM / INVALID_DIFF_AT_1 / INVALID_EXTRA_AT_2 / INVALID_TS_AT_2 /
INVALID_NM_AT_2).
"""
import struct, sys
from ethereum.forks.amsterdam.stateless_ssz import (
    MAX_BYTES_PER_CODE,
    MAX_BYTES_PER_HEADER,
    MAX_BYTES_PER_WITNESS_NODE,
    MAX_PUBLIC_KEYS,
    MAX_WITNESS_CODES,
    MAX_WITNESS_HEADERS,
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
hdr_hex = sys.argv[11]
npr_pbr_hex = sys.argv[12] if len(sys.argv) > 12 else ''
npr_slot_str = sys.argv[13] if len(sys.argv) > 13 else ''

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

HeaderBL = ByteList[MAX_BYTES_PER_HEADER]
HeadersList = SszList[HeaderBL, MAX_WITNESS_HEADERS]
hdr_arg = ()
if hdr_hex in ('INVALID_TS', 'INVALID_NM', 'VALID_TWO', 'VALID_THREE', 'INVALID_DIFF_AT_1', 'INVALID_EXTRA_AT_2', 'INVALID_TS_AT_2', 'INVALID_NM_AT_2', 'VALID_TS_HIBIT', 'VALID_REALISTIC_TWO', 'VALID_EIGHT', 'INVALID_GAS_AT_1', 'INVALID_BLOB_OVERMAX_AT_1', 'INVALID_BLOB_MISALIGN_AT_1'):
    # Multi-header fixtures (N=2 or N=3) exercising K229 and
    # K230 in their accept and reject branches. Each header
    # individually passes K290 / K291 / K240 / K278 / K277.
    #   INVALID_TS   -- non-increasing timestamps, K229 rejects
    #   INVALID_NM   -- non-consecutive numbers, K230 rejects
    #   VALID_TWO    -- N=2 strictly-increasing + consecutive
    #                   numbers; all K-PRs accept.
    #   VALID_THREE  -- N=3 chained headers (parent_hash chain
    #                   computed via keccak256) with strictly-
    #                   increasing timestamps and consecutive
    #                   numbers 1, 2, 3; all K-PRs accept and
    #                   spec's validate_headers ALSO succeeds
    #                   (because contiguity holds), then spec
    #                   STF fails on empty NPR. ELF reaches
    #                   .Lsg_all_pass for the first time at N=3.
    from ethereum.forks.amsterdam.blocks import Header
    from ethereum.forks.amsterdam.fork import EMPTY_OMMER_HASH
    from ethereum_types.bytes import Bytes32, Bytes8, Bytes
    from ethereum_types.numeric import Uint
    from ethereum_types.numeric import U64 as U64t
    from ethereum_types.numeric import U256
    from ethereum.crypto.hash import Hash32
    from ethereum_rlp import rlp
    def mk(number, timestamp):
        return Header(
            parent_hash=Hash32(b'\x00' * 32),
            ommers_hash=EMPTY_OMMER_HASH,
            coinbase=b'\x00' * 20,
            state_root=Hash32(b'\x00' * 32),
            transactions_root=Hash32(b'\x00' * 32),
            receipt_root=Hash32(b'\x00' * 32),
            bloom=b'\x00' * 256,
            difficulty=Uint(0),
            number=Uint(number),
            gas_limit=Uint(1000000),
            gas_used=Uint(0),
            timestamp=U256(timestamp),
            extra_data=Bytes(b''),
            prev_randao=Bytes32(b'\x00' * 32),
            nonce=Bytes8(b'\x00' * 8),
            base_fee_per_gas=Uint(0),
            withdrawals_root=Hash32(b'\x00' * 32),
            blob_gas_used=U64t(0),
            excess_blob_gas=U64t(0),
            parent_beacon_block_root=Hash32(b'\x00' * 32),
            requests_hash=Hash32(b'\x00' * 32),
            block_access_list_hash=Hash32(b'\x00' * 32),
            slot_number=U64t(0),
        )
    if hdr_hex == 'INVALID_TS':
        # Both timestamps 1234 -- K229 requires STRICT increase.
        h0 = mk(1, 1234); h1 = mk(2, 1234)
        hdr_arg = (HeaderBL(rlp.encode(h0)), HeaderBL(rlp.encode(h1)))
    elif hdr_hex == 'INVALID_NM':
        # Numbers 1 and 3 -- not consecutive (should be 2).
        h0 = mk(1, 1234); h1 = mk(3, 2000)
        hdr_arg = (HeaderBL(rlp.encode(h0)), HeaderBL(rlp.encode(h1)))
    elif hdr_hex == 'VALID_TWO':
        # Consecutive numbers (1, 2) and increasing timestamps
        # (1234, 2000). Every K-PR validator accepts.
        h0 = mk(1, 1234); h1 = mk(2, 2000)
        hdr_arg = (HeaderBL(rlp.encode(h0)), HeaderBL(rlp.encode(h1)))
    elif hdr_hex == 'INVALID_DIFF_AT_1':
        # First header valid, second has difficulty=1. K290
        # iterates: first header passes, SECOND fails. Tests
        # the per-header iteration loop body within the K-PR
        # actually checks every header (not just the first).
        def mk_diff(number, timestamp, diff):
            return Header(
                parent_hash=Hash32(b'\x00' * 32),
                ommers_hash=EMPTY_OMMER_HASH,
                coinbase=b'\x00' * 20,
                state_root=Hash32(b'\x00' * 32),
                transactions_root=Hash32(b'\x00' * 32),
                receipt_root=Hash32(b'\x00' * 32),
                bloom=b'\x00' * 256,
                difficulty=Uint(diff),
                number=Uint(number),
                gas_limit=Uint(1000000),
                gas_used=Uint(0),
                timestamp=U256(timestamp),
                extra_data=Bytes(b''),
                prev_randao=Bytes32(b'\x00' * 32),
                nonce=Bytes8(b'\x00' * 8),
                base_fee_per_gas=Uint(0),
                withdrawals_root=Hash32(b'\x00' * 32),
                blob_gas_used=U64t(0),
                excess_blob_gas=U64t(0),
                parent_beacon_block_root=Hash32(b'\x00' * 32),
                requests_hash=Hash32(b'\x00' * 32),
                block_access_list_hash=Hash32(b'\x00' * 32),
                slot_number=U64t(0),
            )
        h0 = mk_diff(1, 1234, 0)
        h1 = mk_diff(2, 2000, 1)  # difficulty != 0 at index 1
        hdr_arg = (HeaderBL(rlp.encode(h0)), HeaderBL(rlp.encode(h1)))
    elif hdr_hex == 'INVALID_GAS_AT_1':
        # First header valid (gas_used <= gas_limit), second
        # header has gas_used > gas_limit. K240 iterates: first
        # header passes the BGTU check, SECOND fails. Tests
        # K240's per-header iteration loop body actually checks
        # every header (closes the iteration-coverage gap for
        # K240 that INVALID_DIFF_AT_1 covers for K290 and
        # INVALID_EXTRA_AT_2 covers for K291). Earlier K-PRs
        # (K290, K291) pass on both headers; the failure is
        # only at K240 on index 1.
        def mk_gas(number, timestamp, gas_used, gas_limit):
            return Header(
                parent_hash=Hash32(b'\x00' * 32),
                ommers_hash=EMPTY_OMMER_HASH,
                coinbase=b'\x00' * 20,
                state_root=Hash32(b'\x00' * 32),
                transactions_root=Hash32(b'\x00' * 32),
                receipt_root=Hash32(b'\x00' * 32),
                bloom=b'\x00' * 256,
                difficulty=Uint(0),
                number=Uint(number),
                gas_limit=Uint(gas_limit),
                gas_used=Uint(gas_used),
                timestamp=U256(timestamp),
                extra_data=Bytes(b''),
                prev_randao=Bytes32(b'\x00' * 32),
                nonce=Bytes8(b'\x00' * 8),
                base_fee_per_gas=Uint(0),
                withdrawals_root=Hash32(b'\x00' * 32),
                blob_gas_used=U64t(0),
                excess_blob_gas=U64t(0),
                parent_beacon_block_root=Hash32(b'\x00' * 32),
                requests_hash=Hash32(b'\x00' * 32),
                block_access_list_hash=Hash32(b'\x00' * 32),
                slot_number=U64t(0),
            )
        h0 = mk_gas(1, 1234, gas_used=0,       gas_limit=1000000)
        h1 = mk_gas(2, 2000, gas_used=1000001, gas_limit=1000000)
        hdr_arg = (HeaderBL(rlp.encode(h0)), HeaderBL(rlp.encode(h1)))
    elif hdr_hex == 'INVALID_BLOB_OVERMAX_AT_1':
        # First header valid (blob_gas_used=0), second has
        # blob_gas_used = 7 * 131072 = 917504. The value is a
        # multiple of GAS_PER_BLOB=131072 (so K278 passes) but
        # exceeds MAX_BLOB_GAS_PER_BLOCK = 6 * 131072 = 786432
        # (so K277 rejects). K290 / K291 / K240 / K278 pass on
        # both headers; K277 iterates -- passes on header 0
        # (0 <= 786432), FAILS on header 1 (917504 > 786432).
        # Closes the K277 iteration coverage gap, completing
        # the per-K-PR iteration matrix begun by
        # INVALID_DIFF_AT_1 (K290), INVALID_EXTRA_AT_2 (K291),
        # INVALID_GAS_AT_1 (K240),
        # INVALID_BLOB_MISALIGN_AT_1 (K278), INVALID_TS_AT_2
        # (K229), INVALID_NM_AT_2 (K230).
        def mk_blob_max(number, timestamp, blob_gas_used):
            return Header(
                parent_hash=Hash32(b'\x00' * 32),
                ommers_hash=EMPTY_OMMER_HASH,
                coinbase=b'\x00' * 20,
                state_root=Hash32(b'\x00' * 32),
                transactions_root=Hash32(b'\x00' * 32),
                receipt_root=Hash32(b'\x00' * 32),
                bloom=b'\x00' * 256,
                difficulty=Uint(0),
                number=Uint(number),
                gas_limit=Uint(1000000),
                gas_used=Uint(0),
                timestamp=U256(timestamp),
                extra_data=Bytes(b''),
                prev_randao=Bytes32(b'\x00' * 32),
                nonce=Bytes8(b'\x00' * 8),
                base_fee_per_gas=Uint(0),
                withdrawals_root=Hash32(b'\x00' * 32),
                blob_gas_used=U64t(blob_gas_used),
                excess_blob_gas=U64t(0),
                parent_beacon_block_root=Hash32(b'\x00' * 32),
                requests_hash=Hash32(b'\x00' * 32),
                block_access_list_hash=Hash32(b'\x00' * 32),
                slot_number=U64t(0),
            )
        h0 = mk_blob_max(1, 1234, blob_gas_used=0)
        h1 = mk_blob_max(2, 2000, blob_gas_used=7 * 131072)  # 917504 > MAX
    elif hdr_hex == 'INVALID_BLOB_MISALIGN_AT_1':
        # First header valid (blob_gas_used=0, trivially a
        # multiple of GAS_PER_BLOB=131072), second header has
        # blob_gas_used=1 -- NOT a multiple of 131072. K290 /
        # K291 / K240 pass on both headers; K278 iterates twice
        # -- passes on header 0, FAILS on header 1. Closes the
        # K278 iteration coverage gap, sister to
        # INVALID_DIFF_AT_1 (K290) / INVALID_EXTRA_AT_2 (K291) /
        # INVALID_GAS_AT_1 (K240) / INVALID_TS_AT_2 (K229) /
        # INVALID_NM_AT_2 (K230). Verifies K278's per-header
        # loop body actually checks every header rather than
        # short-circuiting on the first.
        def mk_blob(number, timestamp, blob_gas_used):
            return Header(
                parent_hash=Hash32(b'\x00' * 32),
                ommers_hash=EMPTY_OMMER_HASH,
                coinbase=b'\x00' * 20,
                state_root=Hash32(b'\x00' * 32),
                transactions_root=Hash32(b'\x00' * 32),
                receipt_root=Hash32(b'\x00' * 32),
                bloom=b'\x00' * 256,
                difficulty=Uint(0),
                number=Uint(number),
                gas_limit=Uint(1000000),
                gas_used=Uint(0),
                timestamp=U256(timestamp),
                extra_data=Bytes(b''),
                prev_randao=Bytes32(b'\x00' * 32),
                nonce=Bytes8(b'\x00' * 8),
                base_fee_per_gas=Uint(0),
                withdrawals_root=Hash32(b'\x00' * 32),
                blob_gas_used=U64t(blob_gas_used),
                excess_blob_gas=U64t(0),
                parent_beacon_block_root=Hash32(b'\x00' * 32),
                requests_hash=Hash32(b'\x00' * 32),
                block_access_list_hash=Hash32(b'\x00' * 32),
                slot_number=U64t(0),
            )
        h0 = mk_blob(1, 1234, blob_gas_used=0)
        h1 = mk_blob(2, 2000, blob_gas_used=1)  # not a multiple of 131072
        hdr_arg = (HeaderBL(rlp.encode(h0)), HeaderBL(rlp.encode(h1)))
    elif hdr_hex == 'INVALID_EXTRA_AT_2':
        # Three headers: 0 and 1 valid, header[2] has
        # extra_data of 33 bytes (over the 32-byte limit).
        # K290 iterates 3 times pass; K291 iterates 3 times,
        # passes on 0 and 1, fails on 2. Tests the K-PR
        # iteration loop body at the LAST index.
        def mk_extra(number, timestamp, extra):
            return Header(
                parent_hash=Hash32(b'\x00' * 32),
                ommers_hash=EMPTY_OMMER_HASH,
                coinbase=b'\x00' * 20,
                state_root=Hash32(b'\x00' * 32),
                transactions_root=Hash32(b'\x00' * 32),
                receipt_root=Hash32(b'\x00' * 32),
                bloom=b'\x00' * 256,
                difficulty=Uint(0),
                number=Uint(number),
                gas_limit=Uint(1000000),
                gas_used=Uint(0),
                timestamp=U256(timestamp),
                extra_data=extra,
                prev_randao=Bytes32(b'\x00' * 32),
                nonce=Bytes8(b'\x00' * 8),
                base_fee_per_gas=Uint(0),
                withdrawals_root=Hash32(b'\x00' * 32),
                blob_gas_used=U64t(0),
                excess_blob_gas=U64t(0),
                parent_beacon_block_root=Hash32(b'\x00' * 32),
                requests_hash=Hash32(b'\x00' * 32),
                block_access_list_hash=Hash32(b'\x00' * 32),
                slot_number=U64t(0),
            )
        h0 = mk_extra(1, 1234, Bytes(b''))
        h1 = mk_extra(2, 2000, Bytes(b''))
        h2 = mk_extra(3, 3000, Bytes(b'\\xab' * 33))
        hdr_arg = (HeaderBL(rlp.encode(h0)), HeaderBL(rlp.encode(h1)),
                   HeaderBL(rlp.encode(h2)))
    elif hdr_hex == 'INVALID_TS_AT_2':
        # Three headers where the FIRST pair has strictly
        # increasing timestamps (1234 < 2000) but the SECOND
        # pair does not (2000 >= 2000). K229 catches between
        # header[1] and header[2]. Tests K229's per-pair
        # loop body at the LAST pair index.
        h0 = mk(1, 1234); h1 = mk(2, 2000); h2 = mk(3, 2000)
        hdr_arg = (HeaderBL(rlp.encode(h0)), HeaderBL(rlp.encode(h1)),
                   HeaderBL(rlp.encode(h2)))
    elif hdr_hex == 'INVALID_NM_AT_2':
        # Three headers where the FIRST pair has consecutive
        # numbers (1 -> 2) but the SECOND pair does not
        # (2 -> 4 instead of 2 -> 3). Timestamps strictly
        # increasing so K229 passes. K230 catches between
        # header[1] and header[2]. Tests K230's per-pair
        # loop body at the LAST pair index.
        h0 = mk(1, 1234); h1 = mk(2, 2000); h2 = mk(4, 3000)
        hdr_arg = (HeaderBL(rlp.encode(h0)), HeaderBL(rlp.encode(h1)),
                   HeaderBL(rlp.encode(h2)))
    elif hdr_hex == 'VALID_REALISTIC_TWO':
        # N=2 chained valid post-merge headers, BOTH with the
        # full VALID_REALISTIC field cohort (every K-PR-ignored
        # field populated with realistic non-zero bytes:
        # parent_hash, coinbase, state_root, txs_root,
        # receipt_root, bloom, prev_randao, base_fee, withdrawals
        # root, excess_blob_gas, parent_beacon_block_root,
        # requests_hash, block_access_list_hash, slot_number).
        # parent_hash chained via keccak256(rlp(h0)) so spec's
        # validate_headers ALSO accepts contiguity. All K-PR
        # validators accept; both reach .Lsg_all_pass.
        #
        # Variety dimension: cross-product of "realistic field
        # cohort" (was only ever N=1) and "chained 2-header"
        # (was only ever minimal-field cohort). Exercises the
        # K-PR pipeline + spec's validate_headers + the realistic
        # RLP-encoded header size (~600 bytes each, ~1200 bytes
        # of witness.headers section) simultaneously.
        from ethereum.crypto.hash import keccak256
        def mk_realistic(number, timestamp, parent_hash):
            return Header(
                parent_hash=parent_hash,
                ommers_hash=EMPTY_OMMER_HASH,
                coinbase=bytes.fromhex('11' * 20),
                state_root=Hash32(bytes.fromhex('22' * 32)),
                transactions_root=Hash32(bytes.fromhex('33' * 32)),
                receipt_root=Hash32(bytes.fromhex('44' * 32)),
                bloom=bytes.fromhex('55' * 256),
                difficulty=Uint(0),
                number=Uint(number),
                gas_limit=Uint(1000000),
                gas_used=Uint(0),
                timestamp=U256(timestamp),
                extra_data=Bytes(b''),
                prev_randao=Bytes32(bytes.fromhex('66' * 32)),
                nonce=Bytes8(b'\x00' * 8),
                base_fee_per_gas=Uint(0x3b9aca00),  # 1 gwei
                withdrawals_root=Hash32(bytes.fromhex('77' * 32)),
                blob_gas_used=U64t(0),
                excess_blob_gas=U64t(0x100000),
                parent_beacon_block_root=Hash32(bytes.fromhex('88' * 32)),
                requests_hash=Hash32(bytes.fromhex('99' * 32)),
                block_access_list_hash=Hash32(bytes.fromhex('cc' * 32)),
                slot_number=U64t(0x1234),
            )
        h0 = mk_realistic(1, 1234, Hash32(b'\x00' * 32))
        h0_bytes = rlp.encode(h0)
        h1 = mk_realistic(2, 2000, keccak256(h0_bytes))
        h1_bytes = rlp.encode(h1)
        hdr_arg = (HeaderBL(h0_bytes), HeaderBL(h1_bytes))
    elif hdr_hex == 'VALID_TS_HIBIT':
        # N=2 chained valid post-merge headers with timestamps
        # that STRADDLE the u64 sign-bit boundary:
        #   ts[0] = 2^63 - 1 = 0x7FFFFFFFFFFFFFFF (max positive
        #                       i64; all bits set except MSB)
        #   ts[1] = 2^63     = 0x8000000000000000 (MSB-only;
        #                       INT64_MIN if interpreted signed)
        # Unsigned: ts[1] > ts[0], so K229 accepts (uses BGEU).
        # Signed:   ts[1] < ts[0], so a buggy BGE swap would
        # incorrectly reject. Regression-guards the timestamp
        # comparator's unsigned-ness.
        # Numbers 1 -> 2 (consecutive), parent_hash chained
        # (keccak256 of RLP(h0)) so spec's validate_headers
        # also succeeds. All other K-PRs pass on both headers.
        from ethereum.crypto.hash import keccak256
        def mk_hibit(number, timestamp, parent_hash):
            return Header(
                parent_hash=parent_hash,
                ommers_hash=EMPTY_OMMER_HASH,
                coinbase=b'\x00' * 20,
                state_root=Hash32(b'\x00' * 32),
                transactions_root=Hash32(b'\x00' * 32),
                receipt_root=Hash32(b'\x00' * 32),
                bloom=b'\x00' * 256,
                difficulty=Uint(0),
                number=Uint(number),
                gas_limit=Uint(1000000),
                gas_used=Uint(0),
                timestamp=U256(timestamp),
                extra_data=Bytes(b''),
                prev_randao=Bytes32(b'\x00' * 32),
                nonce=Bytes8(b'\x00' * 8),
                base_fee_per_gas=Uint(0),
                withdrawals_root=Hash32(b'\x00' * 32),
                blob_gas_used=U64t(0),
                excess_blob_gas=U64t(0),
                parent_beacon_block_root=Hash32(b'\x00' * 32),
                requests_hash=Hash32(b'\x00' * 32),
                block_access_list_hash=Hash32(b'\x00' * 32),
                slot_number=U64t(0),
            )
        h0 = mk_hibit(1, (1 << 63) - 1, Hash32(b'\x00' * 32))
        h0_bytes = rlp.encode(h0)
        h1 = mk_hibit(2, (1 << 63), keccak256(h0_bytes))
        h1_bytes = rlp.encode(h1)
        hdr_arg = (HeaderBL(h0_bytes), HeaderBL(h1_bytes))
    else:  # VALID_THREE
        # Three chained valid post-merge headers. parent_hash
        # chain so spec's validate_headers ALSO accepts
        # (contiguity holds). Strictly-increasing timestamps
        # (1234, 2000, 3000), consecutive numbers (1, 2, 3).
        from ethereum.crypto.hash import keccak256
        def mk_chained(number, timestamp, parent_hash):
            return Header(
                parent_hash=parent_hash,
                ommers_hash=EMPTY_OMMER_HASH,
                coinbase=b'\x00' * 20,
                state_root=Hash32(b'\x00' * 32),
                transactions_root=Hash32(b'\x00' * 32),
                receipt_root=Hash32(b'\x00' * 32),
                bloom=b'\x00' * 256,
                difficulty=Uint(0),
                number=Uint(number),
                gas_limit=Uint(1000000),
                gas_used=Uint(0),
                timestamp=U256(timestamp),
                extra_data=Bytes(b''),
                prev_randao=Bytes32(b'\x00' * 32),
                nonce=Bytes8(b'\x00' * 8),
                base_fee_per_gas=Uint(0),
                withdrawals_root=Hash32(b'\x00' * 32),
                blob_gas_used=U64t(0),
                excess_blob_gas=U64t(0),
                parent_beacon_block_root=Hash32(b'\x00' * 32),
                requests_hash=Hash32(b'\x00' * 32),
                block_access_list_hash=Hash32(b'\x00' * 32),
                slot_number=U64t(0),
            )
        if hdr_hex == 'VALID_EIGHT':
            # N=8 chained valid post-merge headers. Extends the K-PR
            # iteration depth from N=3 (VALID_THREE) to N=8: K229
            # performs 7 pair comparisons, K230 performs 7
            # parent_number + 1 == child_number checks, and each of
            # K290 / K291 / K240 / K278 / K277 iterates over all 8
            # headers individually. parent_hash linkage via
            # keccak256(rlp(h_i)) so spec's validate_headers also
            # accepts contiguity (~4600 bytes of witness.headers).
            nums = list(range(1, 9))
            tss = [1234 + 1000 * i for i in range(8)]
            blobs = []
            prev_hash = Hash32(b'\x00' * 32)
            for i in range(8):
                h = mk_chained(nums[i], tss[i], prev_hash)
                h_bytes = rlp.encode(h)
                blobs.append(HeaderBL(h_bytes))
                prev_hash = keccak256(h_bytes)
            hdr_arg = tuple(blobs)
        else:  # VALID_THREE
            h0 = mk_chained(1, 1234, Hash32(b'\x00' * 32))
            h0_bytes = rlp.encode(h0)
            h1 = mk_chained(2, 2000, keccak256(h0_bytes))
            h1_bytes = rlp.encode(h1)
            h2 = mk_chained(3, 3000, keccak256(h1_bytes))
            h2_bytes = rlp.encode(h2)
            hdr_arg = (HeaderBL(h0_bytes), HeaderBL(h1_bytes), HeaderBL(h2_bytes))
elif hdr_hex in (
    'VALID_POST_MERGE',
    'INVALID_DIFF',
    'INVALID_EXTRA',
    'INVALID_GAS',
    'INVALID_BLOB_MISALIGN',
    'INVALID_BLOB_OVERMAX',
    'VALID_EXTRA_BOUNDARY',
    'VALID_GAS_BOUNDARY',
    'VALID_BLOB_BOUNDARY',
    'VALID_BLOB_MAX_BOUNDARY',
    'INVALID_NONCE',
    'INVALID_OMMERS',
    'VALID_REALISTIC',
    'VALID_ALL_BOUNDARY',
    'VALID_GAS_HIBIT',
):
    # Construct a (mostly) valid post-merge header. Variants:
    #   VALID_POST_MERGE       -- passes all 7 K-PR validators.
    #   INVALID_DIFF           -- difficulty=1; K290 rejects.
    #   INVALID_EXTRA          -- extra_data length 33; K291 rejects.
    #   INVALID_GAS            -- gas_used > gas_limit; K240 rejects.
    #   INVALID_BLOB_MISALIGN  -- blob_gas_used=1 (not a multiple
    #                             of GAS_PER_BLOB=131072); K278
    #                             rejects.
    #   INVALID_BLOB_OVERMAX   -- blob_gas_used = 7 * 131072 =
    #                             917504. Multiple of 131072 so
    #                             K278 passes, but > MAX_BLOB_GAS_
    #                             PER_BLOCK = 6 * 131072 = 786432,
    #                             so K277 rejects.
    #   VALID_EXTRA_BOUNDARY   -- extra_data length EXACTLY 32
    #                             (max allowed); K291 ACCEPTS at
    #                             the boundary.
    from ethereum.forks.amsterdam.blocks import Header
    from ethereum.forks.amsterdam.fork import EMPTY_OMMER_HASH
    from ethereum_types.bytes import Bytes32, Bytes8, Bytes
    from ethereum_types.numeric import Uint
    from ethereum_types.numeric import U64 as U64t
    from ethereum_types.numeric import U256
    from ethereum.crypto.hash import Hash32
    from ethereum_rlp import rlp
    diff = 1 if hdr_hex == 'INVALID_DIFF' else 0
    if hdr_hex in ('INVALID_EXTRA',):
        extra = Bytes(b'\\xab' * 33)
    elif hdr_hex in ('VALID_EXTRA_BOUNDARY', 'VALID_ALL_BOUNDARY'):
        extra = Bytes(b'\\xab' * 32)
    else:
        extra = Bytes(b'')
    if hdr_hex == 'VALID_GAS_HIBIT':
        # Regression guard for K240's unsigned comparison.
        # gas_used = 2^63 - 1 (max positive i64); gas_limit
        # = 2^63 (INT64_MIN if interpreted signed).
        # Unsigned: gas_used < gas_limit -> K240 BGTU correctly
        # accepts. Signed: gas_used (INT64_MAX) > gas_limit
        # (INT64_MIN) -> a buggy BGT swap would reject. The
        # fixture locks in the unsigned-ness of the gas check
        # before the REASON-code surface is reintroduced.
        gas_limit_v = 1 << 63
        gas_used_v = (1 << 63) - 1
    else:
        gas_limit_v = 1000000
        if hdr_hex == 'INVALID_GAS':
            gas_used_v = 1000001
        elif hdr_hex in ('VALID_GAS_BOUNDARY', 'VALID_ALL_BOUNDARY'):
            gas_used_v = 1000000  # == gas_limit, boundary accept
        else:
            gas_used_v = 0
    if hdr_hex == 'INVALID_BLOB_MISALIGN':
        blob_gas_used_v = 1
    elif hdr_hex == 'INVALID_BLOB_OVERMAX':
        blob_gas_used_v = 7 * 131072  # 917504
    elif hdr_hex == 'VALID_BLOB_BOUNDARY':
        blob_gas_used_v = 131072  # one full blob, GAS_PER_BLOB
    elif hdr_hex in ('VALID_BLOB_MAX_BOUNDARY', 'VALID_ALL_BOUNDARY'):
        blob_gas_used_v = 6 * 131072  # 786432 = MAX_BLOB_GAS_PER_BLOCK
    else:
        blob_gas_used_v = 0
    nonce_v = b'\x00\x00\x00\x00\x00\x00\x00\\x01' if hdr_hex == 'INVALID_NONCE' else b'\x00' * 8
    ommers_v = Hash32(b'\\xff' * 32) if hdr_hex == 'INVALID_OMMERS' else EMPTY_OMMER_HASH
    # For VALID_REALISTIC: set K-PR-CHECKED fields to valid values
    # but populate every K-PR-IGNORED field with realistic non-zero
    # bytes. Verifies K-PRs ignore those fields rather than
    # short-circuiting on zero defaults.
    realistic = (hdr_hex == 'VALID_REALISTIC')
    parent_hash_v   = Hash32(bytes.fromhex('aa' * 32))  if realistic else Hash32(b'\x00' * 32)
    coinbase_v      = bytes.fromhex('11' * 20)          if realistic else b'\x00' * 20
    state_root_v    = Hash32(bytes.fromhex('22' * 32))  if realistic else Hash32(b'\x00' * 32)
    txs_root_v      = Hash32(bytes.fromhex('33' * 32))  if realistic else Hash32(b'\x00' * 32)
    receipt_root_v  = Hash32(bytes.fromhex('44' * 32))  if realistic else Hash32(b'\x00' * 32)
    bloom_v         = bytes.fromhex('55' * 256)         if realistic else b'\x00' * 256
    prev_randao_v   = Bytes32(bytes.fromhex('66' * 32)) if realistic else Bytes32(b'\x00' * 32)
    base_fee_v      = Uint(0x3b9aca00)                  if realistic else Uint(0)  # 1 gwei
    withdrawals_v   = Hash32(bytes.fromhex('77' * 32))  if realistic else Hash32(b'\x00' * 32)
    excess_blob_v   = U64t(0x100000)                    if realistic else U64t(0)
    parent_beacon_v = Hash32(bytes.fromhex('88' * 32))  if realistic else Hash32(b'\x00' * 32)
    requests_v      = Hash32(bytes.fromhex('99' * 32))  if realistic else Hash32(b'\x00' * 32)
    bal_v           = Hash32(bytes.fromhex('cc' * 32))  if realistic else Hash32(b'\x00' * 32)
    slot_v          = U64t(0x1234)                      if realistic else U64t(0)
    h = Header(
        parent_hash=parent_hash_v,
        ommers_hash=ommers_v,
        coinbase=coinbase_v,
        state_root=state_root_v,
        transactions_root=txs_root_v,
        receipt_root=receipt_root_v,
        bloom=bloom_v,
        difficulty=Uint(diff),
        number=Uint(1),
        gas_limit=Uint(gas_limit_v),
        gas_used=Uint(gas_used_v),
        timestamp=U256(1234),
        extra_data=extra,
        prev_randao=prev_randao_v,
        nonce=Bytes8(nonce_v),
        base_fee_per_gas=base_fee_v,
        withdrawals_root=withdrawals_v,
        blob_gas_used=U64t(blob_gas_used_v),
        excess_blob_gas=excess_blob_v,
        parent_beacon_block_root=parent_beacon_v,
        requests_hash=requests_v,
        block_access_list_hash=bal_v,
        slot_number=slot_v,
    )
    hdr_arg = (HeaderBL(rlp.encode(h)),)
elif hdr_hex:
    hdr_entries = hdr_hex.split(':')
    hdr_arg = tuple(HeaderBL(bytes.fromhex(h)) for h in hdr_entries)

witness = SszExecutionWitness(
    state=NodesList(*state_arg),
    codes=CodesList(*codes_arg),
    headers=HeadersList(*hdr_arg),
)

PkBV = ByteVector[PUBLIC_KEY_BYTES]
PkList = SszList[PkBV, MAX_PUBLIC_KEYS]
pk_args = ()
if pk_hex:
    pk_entries = pk_hex.split(':')
    pk_args = tuple(PkBV(bytes.fromhex(p)) for p in pk_entries)

npr_kwargs = {}
if npr_pbr_hex:
    from remerkleable.byte_arrays import Bytes32 as Bytes32SSZ
    npr_kwargs['parent_beacon_block_root'] = Bytes32SSZ(bytes.fromhex(npr_pbr_hex))
if npr_slot_str:
    from ethereum.forks.amsterdam.stateless_ssz import SszExecutionPayload
    from remerkleable.basic import uint64 as Uint64SSZ
    npr_kwargs['execution_payload'] = SszExecutionPayload(
        slot_number=Uint64SSZ(int(npr_slot_str, 0)),
    )
npr = SszNewPayloadRequest(**npr_kwargs)

ssz_input = SszStatelessInput(
    new_payload_request=npr,
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
    if pad: f.write(b'\x00' * pad)

# Expected = Python run_stateless_guest output -- the spec entrypoint.
# The Lean ELF should match this byte-for-byte for the current
# empty-input regime.
spec_bytes = bytes(run_stateless_guest(input_bytes))
with open(sys.argv[3], 'w') as f:
    f.write(spec_bytes.hex())
