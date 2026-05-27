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
if hdr_hex in ('INVALID_TS', 'INVALID_NM', 'VALID_TWO', 'VALID_THREE', 'INVALID_DIFF_AT_1', 'INVALID_EXTRA_AT_2', 'INVALID_TS_AT_2', 'INVALID_NM_AT_2'):
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
    if hdr_hex == 'INVALID_EXTRA':
        extra = Bytes(b'\\xab' * 33)
    elif hdr_hex == 'VALID_EXTRA_BOUNDARY':
        extra = Bytes(b'\\xab' * 32)
    else:
        extra = Bytes(b'')
    gas_limit_v = 1000000
    if hdr_hex == 'INVALID_GAS':
        gas_used_v = 1000001
    elif hdr_hex == 'VALID_GAS_BOUNDARY':
        gas_used_v = 1000000  # == gas_limit, boundary accept
    else:
        gas_used_v = 0
    if hdr_hex == 'INVALID_BLOB_MISALIGN':
        blob_gas_used_v = 1
    elif hdr_hex == 'INVALID_BLOB_OVERMAX':
        blob_gas_used_v = 7 * 131072  # 917504
    elif hdr_hex == 'VALID_BLOB_BOUNDARY':
        blob_gas_used_v = 131072  # one full blob, GAS_PER_BLOB
    elif hdr_hex == 'VALID_BLOB_MAX_BOUNDARY':
        blob_gas_used_v = 6 * 131072  # 786432 = MAX_BLOB_GAS_PER_BLOCK
    else:
        blob_gas_used_v = 0
    nonce_v = b'\x00\x00\x00\x00\x00\x00\x00\\x01' if hdr_hex == 'INVALID_NONCE' else b'\x00' * 8
    ommers_v = Hash32(b'\\xff' * 32) if hdr_hex == 'INVALID_OMMERS' else EMPTY_OMMER_HASH
    h = Header(
        parent_hash=Hash32(b'\x00' * 32),
        ommers_hash=ommers_v,
        coinbase=b'\x00' * 20,
        state_root=Hash32(b'\x00' * 32),
        transactions_root=Hash32(b'\x00' * 32),
        receipt_root=Hash32(b'\x00' * 32),
        bloom=b'\x00' * 256,
        difficulty=Uint(diff),
        number=Uint(1),
        gas_limit=Uint(gas_limit_v),
        gas_used=Uint(gas_used_v),
        timestamp=U256(1234),
        extra_data=extra,
        prev_randao=Bytes32(b'\x00' * 32),
        nonce=Bytes8(nonce_v),
        base_fee_per_gas=Uint(0),
        withdrawals_root=Hash32(b'\x00' * 32),
        blob_gas_used=U64t(blob_gas_used_v),
        excess_blob_gas=U64t(0),
        parent_beacon_block_root=Hash32(b'\x00' * 32),
        requests_hash=Hash32(b'\x00' * 32),
        block_access_list_hash=Hash32(b'\x00' * 32),
        slot_number=U64t(0),
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
    if pad: f.write(b'\x00' * pad)

# Expected = Python run_stateless_guest output -- the spec entrypoint.
# The Lean ELF should match this byte-for-byte for the current
# empty-input regime.
spec_bytes = bytes(run_stateless_guest(input_bytes))
with open(sys.argv[3], 'w') as f:
    f.write(spec_bytes.hex())
