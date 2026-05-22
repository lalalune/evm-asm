/-
  EvmAsm.Stateless.Transaction.Decode

  Decode an Ethereum transaction from its RLP-encoded bytes.
  Mirrors Python's `decode_transaction` from
  `forks/amsterdam/transactions.py`.

  ## Wire format (post-Berlin)

  Type-prefix dispatch:
    - Byte 0 == 0x01: EIP-2930 access list (LegacyAccessList)
    - Byte 0 == 0x02: EIP-1559 dynamic fee
    - Byte 0 == 0x03: EIP-4844 blob
    - Byte 0 == 0x04: EIP-7702 set code
    - Else: legacy (full RLP from byte 0)

  Each type has its own RLP body shape (different number of
  fields, different ordering). The decoder dispatches and lifts
  into a flat in-memory tx struct (PR-K11 uses a per-type
  scratch slot).

  ## EIP-7702 / 4844 caveats

  PR-K11 scaffolds these but the implementation routes both to
  `unimplemented_exit` with reason `REASON_EIP7702_DELEGATION`
  or `REASON_EIP4844_BLOB`. (See PR1 / `Stateless.Unimplemented`.)
  PR-K1x lifts the restrictions once we have ECRECOVER and KZG
  in scope.

  ## PR-K36 status

  The legacy-tx decoder lands first, in
  `EvmAsm.Codegen.Programs.txLegacyDecodeFunction`. Decodes the
  9-field RLP list into a 196-byte output struct:

      offset  0..  8  nonce (u64 LE)
      offset  8.. 40  gas_price (u256 BE, left-zero-padded)
      offset 40.. 48  gas_limit (u64 LE)
      offset 48.. 68  to (20-byte address; zero on creation)
      offset 68.. 76  to_present (u64; 0 if creation, 1 if call)
      offset 76..108  value (u256 BE)
      offset 108..116 data_offset (within tx_rlp)
      offset 116..124 data_length
      offset 124..132 v (u64 LE)
      offset 132..164 r (u256 BE)
      offset 164..196 s (u256 BE)

  Type-prefixed tx forms (EIP-1559 / 2930 / 4844 / 7702) land
  in follow-up PRs that wrap this legacy decoder and add the
  per-type field re-ordering.

  Calling convention:

      Input:
        a0 (input)  : tx_rlp ptr
        a1 (input)  : tx_rlp byte length
        a2 (input)  : 196-byte output struct ptr
        ra (input)  : return

      Output:
        a0 = 0  success; all 9 fields written
        a0 = 1  parse failure (not a 9-item list, field too long,
                or `to` is neither 0 nor 20 bytes).

  ## PR-K40 status: tx_type_dispatch

  Reads byte 0 of the tx envelope and returns
  `(tx_type, inner_offset)`. Lets the caller route the inner RLP
  body to the correct per-type decoder. Lives at
  `EvmAsm.Codegen.Programs.txTypeDispatchFunction`.

  ## PR-K41 status: tx_eip1559_decode

  Decodes the 12-field inner RLP body of an EIP-1559 (type-2)
  transaction into a flat 248-byte output struct. Caller is
  expected to have stripped the 0x02 type byte (PR-K40 reports
  the inner offset). Lives at
  `EvmAsm.Codegen.Programs.txEip1559DecodeFunction`.

      offset  0..  8  chain_id (u64 LE)
      offset  8.. 16  nonce (u64 LE)
      offset 16.. 48  max_priority_fee_per_gas (u256 BE)
      offset 48.. 80  max_fee_per_gas (u256 BE)
      offset 80.. 88  gas_limit (u64 LE)
      offset 88..108  to (20-byte address; zero on creation)
      offset 108..112 to_present (u32; 0 if creation, 1 if call)
      offset 112..144 value (u256 BE)
      offset 144..152 data_offset (within inner_rlp)
      offset 152..160 data_length
      offset 160..168 access_list_offset (whole encoded sub-list
                                          incl. RLP prefix)
      offset 168..176 access_list_length
      offset 176..184 y_parity (u64 LE)
      offset 184..216 r (u256 BE)
      offset 216..248 s (u256 BE)
-/

namespace EvmAsm.Stateless.Transaction.Decode

-- TODO(stateless-tx): EIP-2930 (type 1), EIP-4844 (type 3),
-- and EIP-7702 (type 4) inner decoders, mirroring PR-K41's
-- `tx_eip1559_decode` shape.

end EvmAsm.Stateless.Transaction.Decode
