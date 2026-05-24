/-
  EvmAsm.Codegen.Programs.Header

  Block-header decoding and validation cluster lifted out of
  `EvmAsm.Codegen.Programs` per the file-size hard cap.

  Header decoders:
    K38  header_minimal_decode
    K39  header_extended_decode
    K55  coinbase_extract_from_header
    K90  header_extract_blob_gas_pair
    K93  block_validate_blob_gas_max_cap
    K95  header_extract_block_roots

  Header validators:
    K43  validate_header_basic
    K72  check_gas_limit
    K63  calc_excess_blob_gas
    K67  header_validate_post_merge
    K68  header_validate_extra_data_length

  Pre- / post-exec account mutations (placed adjacently in the
  source file; they consume the header-validation pipeline's
  outputs for gas / base-fee fields):
    K81  account_charge_gas_pre_exec
    K82  account_refund_gas_post_exec

  Header fee-validation chain:
    K73  eip1559_calc_base_fee_per_gas
    K74  header_validate_base_fee
    K75  validate_header_full

  No proofs yet -- these are codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.Tx

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## header_minimal_decode -- PR-K38

    Decode the 4 STF-essential fields of an RLP-encoded
    Ethereum block header into a flat 96-byte output struct:

       0..32   parent_hash    (RLP field 0)
      32..64   state_root     (RLP field 3)
      64..72   number (u64)   (RLP field 8)
      72..80   timestamp(u64) (RLP field 11; rejected if > 8 B)

    Header RLP field count varies by fork (15..22 fields).
    This decoder reads only the first 12 fields' indices, so
    it works on any post-Berlin header.

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp byte length
      a2 (input)  : 96-byte output struct ptr
      ra (input)  : return
      a0 (output) : 0 success / 1 parse fail (not an RLP list,
                    parent_hash or state_root not 32 bytes,
                    or timestamp > 8 bytes BE).

    Composes PR-K20 `rlp_list_nth_item` + PR-K34
    `rlp_field_to_u64`. The hash fields are copied via 4 ×
    8-byte `ld`/`sd` (each 32-byte hash). -/
def headerMinimalDecodeFunction : String :=
  "header_minimal_decode:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0                  # header_rlp ptr\n" ++
  "  mv s1, a1                  # header_len\n" ++
  "  mv s2, a2                  # struct out\n" ++
  "  # Field 0: parent_hash (32 bytes)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 0\n" ++
  "  la a3, hmd_offset; la a4, hmd_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lhmd_fail\n" ++
  "  la t0, hmd_length; ld t1, 0(t0)\n" ++
  "  li t2, 32\n" ++
  "  bne t1, t2, .Lhmd_fail\n" ++
  "  la t0, hmd_offset; ld t3, 0(t0); add t3, s0, t3\n" ++
  "  ld t4,  0(t3); sd t4,  0(s2)\n" ++
  "  ld t4,  8(t3); sd t4,  8(s2)\n" ++
  "  ld t4, 16(t3); sd t4, 16(s2)\n" ++
  "  ld t4, 24(t3); sd t4, 24(s2)\n" ++
  "  # Field 3: state_root (32 bytes at struct + 32)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 3\n" ++
  "  la a3, hmd_offset; la a4, hmd_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lhmd_fail\n" ++
  "  la t0, hmd_length; ld t1, 0(t0)\n" ++
  "  li t2, 32\n" ++
  "  bne t1, t2, .Lhmd_fail\n" ++
  "  la t0, hmd_offset; ld t3, 0(t0); add t3, s0, t3\n" ++
  "  addi t4, s2, 32\n" ++
  "  ld t5,  0(t3); sd t5,  0(t4)\n" ++
  "  ld t5,  8(t3); sd t5,  8(t4)\n" ++
  "  ld t5, 16(t3); sd t5, 16(t4)\n" ++
  "  ld t5, 24(t3); sd t5, 24(t4)\n" ++
  "  # Field 8: number (u64 at struct + 64)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 8\n" ++
  "  addi a3, s2, 64\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lhmd_fail\n" ++
  "  # Field 11: timestamp (u64 at struct + 72)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 11\n" ++
  "  addi a3, s2, 72\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lhmd_fail\n" ++
  "  li a0, 0\n" ++
  "  j .Lhmd_ret\n" ++
  ".Lhmd_fail:\n" ++
  "  li a0, 1\n" ++
  ".Lhmd_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_header_minimal_decode`: probe BuildUnit. Reads
    (header_len, header_bytes) from host input, writes
    (status, 96-byte struct) to OUTPUT. -/
def ziskHeaderMinimalDecodePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # header_len\n" ++
  "  addi a0, a3, 16             # header ptr\n" ++
  "  li a2, 0xa0010008           # struct at OUTPUT + 8\n" ++
  "  # Pre-zero 96 bytes.\n" ++
  "  mv t0, a2; li t1, 12\n" ++
  ".Lhmd_zinit:\n" ++
  "  beqz t1, .Lhmd_zdone\n" ++
  "  sd zero, 0(t0)\n" ++
  "  addi t0, t0, 8\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Lhmd_zinit\n" ++
  ".Lhmd_zdone:\n" ++
  "  jal ra, header_minimal_decode\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lhmd_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  headerMinimalDecodeFunction ++ "\n" ++
  ".Lhmd_pdone:"

def ziskHeaderMinimalDecodeDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "hmd_offset:\n" ++
  "  .zero 8\n" ++
  "hmd_length:\n" ++
  "  .zero 8"

def ziskHeaderMinimalDecodeProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskHeaderMinimalDecodePrologue
  dataAsm     := ziskHeaderMinimalDecodeDataSection
}

/-! ## header_extended_decode -- PR-K39

    Extends PR-K38 `header_minimal_decode` with three more
    STF-essential fields:

       0..32   parent_hash    (field 0)
      32..64   state_root     (field 3)
      64..72   number         (field 8, u64)
      72..80   timestamp      (field 11, u64)
      80..88   gas_limit      (field 9, u64)
      88..96   gas_used       (field 10, u64)
      96..128  base_fee_per_gas (field 15, u256 BE)

    The base_fee_per_gas field exists from EIP-1559 (London)
    onward. Headers older than London don't have it; this
    function rejects (status=1) if field 15 doesn't exist.

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header byte length
      a2 (input)  : 128-byte output struct ptr
      ra (input)  : return
      a0 (output) : 0 success / 1 parse fail. -/
def headerExtendedDecodeFunction : String :=
  "header_extended_decode:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0                  # header_rlp ptr\n" ++
  "  mv s1, a1                  # header_len\n" ++
  "  mv s2, a2                  # struct out\n" ++
  "  # Field 0: parent_hash\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 0\n" ++
  "  la a3, hmd_offset; la a4, hmd_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lhed_fail\n" ++
  "  la t0, hmd_length; ld t1, 0(t0)\n" ++
  "  li t2, 32\n" ++
  "  bne t1, t2, .Lhed_fail\n" ++
  "  la t0, hmd_offset; ld t3, 0(t0); add t3, s0, t3\n" ++
  "  ld t4,  0(t3); sd t4,  0(s2)\n" ++
  "  ld t4,  8(t3); sd t4,  8(s2)\n" ++
  "  ld t4, 16(t3); sd t4, 16(s2)\n" ++
  "  ld t4, 24(t3); sd t4, 24(s2)\n" ++
  "  # Field 3: state_root\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 3\n" ++
  "  la a3, hmd_offset; la a4, hmd_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lhed_fail\n" ++
  "  la t0, hmd_length; ld t1, 0(t0)\n" ++
  "  li t2, 32\n" ++
  "  bne t1, t2, .Lhed_fail\n" ++
  "  la t0, hmd_offset; ld t3, 0(t0); add t3, s0, t3\n" ++
  "  addi t4, s2, 32\n" ++
  "  ld t5,  0(t3); sd t5,  0(t4)\n" ++
  "  ld t5,  8(t3); sd t5,  8(t4)\n" ++
  "  ld t5, 16(t3); sd t5, 16(t4)\n" ++
  "  ld t5, 24(t3); sd t5, 24(t4)\n" ++
  "  # Field 8: number\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 8\n" ++
  "  addi a3, s2, 64\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lhed_fail\n" ++
  "  # Field 11: timestamp\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 11\n" ++
  "  addi a3, s2, 72\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lhed_fail\n" ++
  "  # Field 9: gas_limit\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 9\n" ++
  "  addi a3, s2, 80\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lhed_fail\n" ++
  "  # Field 10: gas_used\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 10\n" ++
  "  addi a3, s2, 88\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lhed_fail\n" ++
  "  # Field 15: base_fee_per_gas (u256)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 15\n" ++
  "  addi a3, s2, 96\n" ++
  "  jal ra, rlp_field_to_u256_be\n" ++
  "  bnez a0, .Lhed_fail\n" ++
  "  li a0, 0\n" ++
  "  j .Lhed_ret\n" ++
  ".Lhed_fail:\n" ++
  "  li a0, 1\n" ++
  ".Lhed_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_header_extended_decode`: probe BuildUnit. -/
def ziskHeaderExtendedDecodePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # header_len\n" ++
  "  addi a0, a3, 16             # header ptr\n" ++
  "  li a2, 0xa0010008           # struct at OUTPUT + 8\n" ++
  "  # Pre-zero 128 bytes.\n" ++
  "  mv t0, a2; li t1, 16\n" ++
  ".Lhed_zinit:\n" ++
  "  beqz t1, .Lhed_zdone\n" ++
  "  sd zero, 0(t0)\n" ++
  "  addi t0, t0, 8\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Lhed_zinit\n" ++
  ".Lhed_zdone:\n" ++
  "  jal ra, header_extended_decode\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lhed_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  rlpFieldToU256BeFunction ++ "\n" ++
  headerExtendedDecodeFunction ++ "\n" ++
  ".Lhed_pdone:"

def ziskHeaderExtendedDecodeDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "hmd_offset:\n" ++
  "  .zero 8\n" ++
  "hmd_length:\n" ++
  "  .zero 8"

def ziskHeaderExtendedDecodeProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskHeaderExtendedDecodePrologue
  dataAsm     := ziskHeaderExtendedDecodeDataSection
}

/-! ## coinbase_extract_from_header -- PR-K55 beneficiary getter

    Extract the 20-byte beneficiary (coinbase) address — field 2
    of an RLP-encoded block header. Direct input to
    `process_transaction`'s priority-fee credit:

      coinbase.balance += effective_priority_fee × gas_used

    The header decoders PR-K38 / PR-K39 read parent_hash,
    state_root, gas_limit, gas_used, etc., but skip the
    beneficiary since it isn't part of the STF skeleton's
    minimal/extended struct. This helper is the dedicated getter
    for callers that only need the coinbase.

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp byte length
      a2 (input)  : 20-byte output ptr (caller-supplied)
      ra (input)  : return
      a0 (output) : 0 success / 1 parse fail (not a list or field
                    2 not 20 bytes). On failure, output is zeroed.

    Composes PR-K20 `rlp_list_nth_item`. Uses two 8-byte `.data`
    scratch slots (`ceh_offset`, `ceh_length`). -/
def coinbaseExtractFromHeaderFunction : String :=
  "coinbase_extract_from_header:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0                  # header_rlp ptr\n" ++
  "  mv s1, a1                  # header_len\n" ++
  "  mv s2, a2                  # output 20B ptr\n" ++
  "  # Get field 2 (coinbase) bounds.\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 2\n" ++
  "  la a3, ceh_offset; la a4, ceh_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lceh_fail\n" ++
  "  la t0, ceh_length; ld t1, 0(t0)\n" ++
  "  li t2, 20\n" ++
  "  bne t1, t2, .Lceh_fail\n" ++
  "  la t0, ceh_offset; ld t3, 0(t0); add t3, s0, t3\n" ++
  "  # Copy 20 bytes: 8 + 8 + 4 = 20.\n" ++
  "  ld t4,  0(t3); sd t4,  0(s2)\n" ++
  "  ld t4,  8(t3); sd t4,  8(s2)\n" ++
  "  lwu t4, 16(t3); sw t4, 16(s2)\n" ++
  "  li a0, 0\n" ++
  "  j .Lceh_ret\n" ++
  ".Lceh_fail:\n" ++
  "  sd zero,  0(s2); sd zero, 8(s2); sw zero, 16(s2)\n" ++
  "  li a0, 1\n" ++
  ".Lceh_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_coinbase_extract_from_header`: probe BuildUnit. Reads
    (header_len, header_bytes) from host input, writes
    (status, 20B address + 4B pad) to OUTPUT (32 bytes total). -/
def ziskCoinbaseExtractFromHeaderPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # header_len\n" ++
  "  addi a0, a3, 16             # header ptr\n" ++
  "  li a2, 0xa0010008           # 20B output at OUTPUT + 8\n" ++
  "  # Pre-zero the 20B output + 4B trailing pad.\n" ++
  "  mv t0, a2\n" ++
  "  sd zero, 0(t0); sd zero, 8(t0); sw zero, 16(t0)\n" ++
  "  jal ra, coinbase_extract_from_header\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lceh_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  coinbaseExtractFromHeaderFunction ++ "\n" ++
  ".Lceh_pdone:"

def ziskCoinbaseExtractFromHeaderDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "ceh_offset:\n" ++
  "  .zero 8\n" ++
  "ceh_length:\n" ++
  "  .zero 8"

def ziskCoinbaseExtractFromHeaderProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskCoinbaseExtractFromHeaderPrologue
  dataAsm     := ziskCoinbaseExtractFromHeaderDataSection
}

/-! ## header_extract_blob_gas_pair -- PR-K90 Cancun blob fields

    Extract the EIP-4844 blob-gas fields from an Amsterdam header:

      blob_gas_used    (header field 17, u64) — total blob gas
        consumed by all transactions in this block (= sum of
        `len(tx.blob_versioned_hashes) × GAS_PER_BLOB` over type-3
        txs). Cross-checks against PR-K89.

      excess_blob_gas  (header field 18, u64) — running total used
        for the blob-fee adjustment formula.

    Cancun-era (and later) headers always have both. Pre-Cancun
    headers don't, and the extractor reports a parse failure.

    Direct inputs to:
      * the apply_body invariant
        `header.blob_gas_used == sum(tx.blob_gas_used)`
      * the next-block `excess_blob_gas` recurrence used in
        `calculate_excess_blob_gas`.

    Output layout (16 bytes):
       0..  8  blob_gas_used    (u64 LE)
       8.. 16  excess_blob_gas  (u64 LE)

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp byte length
      a2 (input)  : 16-byte output ptr (caller-supplied)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : header parse failed / field 17 missing / not u64
        2 : field 18 missing / not u64

    Composes PR-K20 `rlp_list_nth_item` via PR-K53
    `rlp_field_to_u64`. Uses two 8-byte `.data` scratch slots
    (`rfu_offset`, `rfu_length`) shared with other K-helpers. -/
def headerExtractBlobGasPairFunction : String :=
  "header_extract_blob_gas_pair:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0                  # header_rlp ptr\n" ++
  "  mv s1, a1                  # header_len\n" ++
  "  mv s2, a2                  # output 16B ptr\n" ++
  "  # Field 17: blob_gas_used → out[0..8]\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 17\n" ++
  "  mv a3, s2\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  beqz a0, .Lhebgp_f18\n" ++
  "  sd zero, 0(s2); sd zero, 8(s2)\n" ++
  "  li a0, 1\n" ++
  "  j .Lhebgp_ret\n" ++
  ".Lhebgp_f18:\n" ++
  "  # Field 18: excess_blob_gas → out[8..16]\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 18\n" ++
  "  addi a3, s2, 8\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  beqz a0, .Lhebgp_ok\n" ++
  "  sd zero, 0(s2); sd zero, 8(s2)\n" ++
  "  li a0, 2\n" ++
  "  j .Lhebgp_ret\n" ++
  ".Lhebgp_ok:\n" ++
  "  li a0, 0\n" ++
  ".Lhebgp_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_header_extract_blob_gas_pair`: probe BuildUnit. Reads
    (header_len, header_bytes), writes (status, blob_gas_used,
    excess_blob_gas) to OUTPUT (24 bytes total). -/
def ziskHeaderExtractBlobGasPairPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # header_len\n" ++
  "  addi a0, a3, 16             # header ptr\n" ++
  "  li a2, 0xa0010008           # 16B output at OUTPUT + 8\n" ++
  "  sd zero, 0(a2); sd zero, 8(a2)\n" ++
  "  jal ra, header_extract_blob_gas_pair\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lhebgp_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  headerExtractBlobGasPairFunction ++ "\n" ++
  ".Lhebgp_pdone:"

def ziskHeaderExtractBlobGasPairDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8"

def ziskHeaderExtractBlobGasPairProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskHeaderExtractBlobGasPairPrologue
  dataAsm     := ziskHeaderExtractBlobGasPairDataSection
}

/-! ## block_validate_blob_gas_max_cap -- PR-K93

    Cancun cap enforcement: a block's `blob_gas_used` cannot exceed
    `MAX_BLOB_GAS_PER_BLOCK = BLOB_SCHEDULE_MAX × GAS_PER_BLOB`.

    Python reference (`forks/amsterdam/fork.py`):

      MAX_BLOB_GAS_PER_BLOCK = BLOB_SCHEDULE_MAX * GAS_PER_BLOB
      blob_gas_available = MAX_BLOB_GAS_PER_BLOCK - block_output.blob_gas_used
      # …enforced per-tx as `tx_blob_gas_used > blob_gas_available`

    The block-level cap is the loop invariant: at end-of-block,
    `block_output.blob_gas_used == header.blob_gas_used`, so the
    consensus check that `header.blob_gas_used ≤ MAX_BLOB_GAS_PER_BLOCK`
    is the closed form. On Amsterdam mainnet:

      MAX_BLOB_GAS_PER_BLOCK = 21 × 131072 = 2,752,512

    Both parameters are passed in so the helper works across
    forks that adjust either.

    Computation:
      1. Extract `header.blob_gas_used` (field 17, u64) via PR-K53
         `rlp_field_to_u64`.
      2. Compute `cap = max_blobs_per_block × gas_per_blob`; reject
         on u64 overflow.
      3. Compare `blob_gas_used ≤ cap`.

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp byte length
      a2 (input)  : max_blobs_per_block (u64; 21 on mainnet Amsterdam)
      a3 (input)  : gas_per_blob (u64; 131072 on mainnet)
      ra (input)  : return
      a0 (output) : composite status

    Status encoding:
      0 : within cap
      1 : header parse / field 17 missing / not u64
      2 : `max_blobs_per_block × gas_per_blob` overflows u64
      3 : `blob_gas_used > cap`

    Composes PR-K20 `rlp_list_nth_item` via PR-K53
    `rlp_field_to_u64`. -/
def blockValidateBlobGasMaxCapFunction : String :=
  "block_validate_blob_gas_max_cap:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a2                   # max_blobs_per_block\n" ++
  "  mv s1, a3                   # gas_per_blob\n" ++
  "  # Step 1: extract header.blob_gas_used (field 17, u64).\n" ++
  "  # a0,a1 still hold (header_ptr, header_len).\n" ++
  "  li a2, 17\n" ++
  "  la a3, bvbmc_bgu\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  beqz a0, .Lbvbmc_step2\n" ++
  "  li a0, 1\n" ++
  "  j .Lbvbmc_ret\n" ++
  ".Lbvbmc_step2:\n" ++
  "  # Step 2: cap = max_blobs × gas_per_blob, with u64 overflow check.\n" ++
  "  mulhu t0, s0, s1            # high half of unsigned product\n" ++
  "  bnez t0, .Lbvbmc_overflow\n" ++
  "  mul s2, s0, s1              # cap (low 64 bits)\n" ++
  "  # Step 3: compare blob_gas_used <= cap.\n" ++
  "  la t0, bvbmc_bgu\n" ++
  "  ld t1, 0(t0)\n" ++
  "  bgtu t1, s2, .Lbvbmc_exceeds\n" ++
  "  li a0, 0\n" ++
  "  j .Lbvbmc_ret\n" ++
  ".Lbvbmc_overflow:\n" ++
  "  li a0, 2\n" ++
  "  j .Lbvbmc_ret\n" ++
  ".Lbvbmc_exceeds:\n" ++
  "  li a0, 3\n" ++
  ".Lbvbmc_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_block_validate_blob_gas_max_cap`: probe BuildUnit. Reads
    (header_len, max_blobs, gas_per_blob, header_bytes) from host
    input, writes 8-byte status to OUTPUT. -/
def ziskBlockValidateBlobGasMaxCapPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a4, 0x40000000\n" ++
  "  ld a1, 8(a4)                # header_len\n" ++
  "  ld a2, 16(a4)               # max_blobs_per_block\n" ++
  "  ld a3, 24(a4)               # gas_per_blob\n" ++
  "  addi a0, a4, 32             # header_ptr\n" ++
  "  jal ra, block_validate_blob_gas_max_cap\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lbvbmc_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  blockValidateBlobGasMaxCapFunction ++ "\n" ++
  ".Lbvbmc_pdone:"

def ziskBlockValidateBlobGasMaxCapDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "bvbmc_bgu:\n" ++
  "  .zero 8"

def ziskBlockValidateBlobGasMaxCapProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBlockValidateBlobGasMaxCapPrologue
  dataAsm     := ziskBlockValidateBlobGasMaxCapDataSection
}

/-! ## header_extract_block_roots -- PR-K95

    Extract the three remaining 32-byte root fields from an
    Amsterdam header that the existing extended-decode helpers
    don't cover:

       0..32   transactions_root  (field 4)
      32..64   receipt_root       (field 5)
      64..96   withdrawals_root   (field 16)

    Used by `validate_block_body` callers that cross-check the
    body's tx/receipt/withdrawal MPT roots against the consensus-
    layer commitment, and by the trie-rebuild path. The state_root
    (field 3) is already covered by PR-K39 `header_extended_decode`;
    `parent_hash` by PR-K17; `coinbase` by PR-K55.

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp byte length
      a2 (input)  : 96-byte output ptr (caller-supplied)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : field 4 (transactions_root) missing / not 32 B
        2 : field 5 (receipt_root) missing / not 32 B
        3 : field 16 (withdrawals_root) missing / not 32 B
            (pre-Shanghai headers don't have this field)

    Composes PR-K20 `rlp_list_nth_item`. Uses two 8-byte `.data`
    scratch slots (`hebr_offset`, `hebr_length`). -/
def headerExtractBlockRootsFunction : String :=
  "header_extract_block_roots:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0                  # header_rlp ptr\n" ++
  "  mv s1, a1                  # header_len\n" ++
  "  mv s2, a2                  # 96B output ptr\n" ++
  "  # Field 4: transactions_root → out[0..32]\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 4\n" ++
  "  la a3, hebr_offset; la a4, hebr_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lhebr_f4_fail\n" ++
  "  la t0, hebr_length; ld t1, 0(t0)\n" ++
  "  li t2, 32\n" ++
  "  bne t1, t2, .Lhebr_f4_fail\n" ++
  "  la t0, hebr_offset; ld t3, 0(t0); add t3, s0, t3\n" ++
  "  ld t4,  0(t3); sd t4,  0(s2)\n" ++
  "  ld t4,  8(t3); sd t4,  8(s2)\n" ++
  "  ld t4, 16(t3); sd t4, 16(s2)\n" ++
  "  ld t4, 24(t3); sd t4, 24(s2)\n" ++
  "  # Field 5: receipt_root → out[32..64]\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 5\n" ++
  "  la a3, hebr_offset; la a4, hebr_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lhebr_f5_fail\n" ++
  "  la t0, hebr_length; ld t1, 0(t0)\n" ++
  "  li t2, 32\n" ++
  "  bne t1, t2, .Lhebr_f5_fail\n" ++
  "  la t0, hebr_offset; ld t3, 0(t0); add t3, s0, t3\n" ++
  "  addi t5, s2, 32\n" ++
  "  ld t4,  0(t3); sd t4,  0(t5)\n" ++
  "  ld t4,  8(t3); sd t4,  8(t5)\n" ++
  "  ld t4, 16(t3); sd t4, 16(t5)\n" ++
  "  ld t4, 24(t3); sd t4, 24(t5)\n" ++
  "  # Field 16: withdrawals_root → out[64..96]\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 16\n" ++
  "  la a3, hebr_offset; la a4, hebr_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lhebr_f16_fail\n" ++
  "  la t0, hebr_length; ld t1, 0(t0)\n" ++
  "  li t2, 32\n" ++
  "  bne t1, t2, .Lhebr_f16_fail\n" ++
  "  la t0, hebr_offset; ld t3, 0(t0); add t3, s0, t3\n" ++
  "  addi t5, s2, 64\n" ++
  "  ld t4,  0(t3); sd t4,  0(t5)\n" ++
  "  ld t4,  8(t3); sd t4,  8(t5)\n" ++
  "  ld t4, 16(t3); sd t4, 16(t5)\n" ++
  "  ld t4, 24(t3); sd t4, 24(t5)\n" ++
  "  li a0, 0\n" ++
  "  j .Lhebr_ret\n" ++
  ".Lhebr_f4_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lhebr_zero_ret\n" ++
  ".Lhebr_f5_fail:\n" ++
  "  li a0, 2\n" ++
  "  j .Lhebr_zero_ret\n" ++
  ".Lhebr_f16_fail:\n" ++
  "  li a0, 3\n" ++
  ".Lhebr_zero_ret:\n" ++
  "  # Zero the output on any failure.\n" ++
  "  mv t0, s2; li t1, 12\n" ++
  ".Lhebr_zero:\n" ++
  "  beqz t1, .Lhebr_ret\n" ++
  "  sd zero, 0(t0); addi t0, t0, 8; addi t1, t1, -1\n" ++
  "  j .Lhebr_zero\n" ++
  ".Lhebr_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_header_extract_block_roots`: probe BuildUnit. Reads
    (header_len, header_bytes), writes (status, 3 × 32-byte roots)
    to OUTPUT (104 bytes total). -/
def ziskHeaderExtractBlockRootsPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # header_len\n" ++
  "  addi a0, a3, 16             # header ptr\n" ++
  "  li a2, 0xa0010008           # 96B output at OUTPUT + 8\n" ++
  "  # Pre-zero 96 bytes (12 dwords).\n" ++
  "  mv t0, a2; li t1, 12\n" ++
  ".Lhebr_pzero:\n" ++
  "  beqz t1, .Lhebr_pzdone\n" ++
  "  sd zero, 0(t0); addi t0, t0, 8; addi t1, t1, -1\n" ++
  "  j .Lhebr_pzero\n" ++
  ".Lhebr_pzdone:\n" ++
  "  jal ra, header_extract_block_roots\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lhebr_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  headerExtractBlockRootsFunction ++ "\n" ++
  ".Lhebr_pdone:"

def ziskHeaderExtractBlockRootsDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "hebr_offset:\n" ++
  "  .zero 8\n" ++
  "hebr_length:\n" ++
  "  .zero 8"

def ziskHeaderExtractBlockRootsProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskHeaderExtractBlockRootsPrologue
  dataAsm     := ziskHeaderExtractBlockRootsDataSection
}

/-! ## validate_header_basic -- PR-K43 per-header semantic checks

    Three u64 invariants from `validate_header` (Python:
    `forks/amsterdam/fork.py`):

      1. gas_used <= gas_limit
      2. number == parent.number + 1
      3. timestamp > parent.timestamp

    Both inputs are 128-byte extended-header structs as produced
    by PR-K39 `header_extended_decode`. Only the u64 fields at
    offsets 64 (number), 72 (timestamp), 80 (gas_limit), 88
    (gas_used) are read; the hash fields (parent_hash,
    state_root) and base_fee_per_gas are ignored here -- those
    are checked elsewhere (PR-K18 `validate_chain` for the hash
    chain, future PR for the EIP-1559 base-fee formula).

    Calling convention:
      a0 (input)  : header_ptr (128-byte struct, this header)
      a1 (input)  : parent_ptr (128-byte struct, parent header)
      ra (input)  : return
      a0 (output) : 0 ok
                    1 gas_used > gas_limit
                    2 number != parent.number + 1
                    3 timestamp <= parent.timestamp

    Pure register arithmetic, no scratch memory, leaf-callable. -/
def validateHeaderBasicFunction : String :=
  "validate_header_basic:\n" ++
  "  ld t0, 88(a0)              # this.gas_used\n" ++
  "  ld t1, 80(a0)              # this.gas_limit\n" ++
  "  bgtu t0, t1, .Lvhb_fail_gas\n" ++
  "  ld t0, 64(a0)              # this.number\n" ++
  "  ld t1, 64(a1)              # parent.number\n" ++
  "  addi t1, t1, 1\n" ++
  "  bne t0, t1, .Lvhb_fail_number\n" ++
  "  ld t0, 72(a0)              # this.timestamp\n" ++
  "  ld t1, 72(a1)              # parent.timestamp\n" ++
  "  bgeu t1, t0, .Lvhb_fail_timestamp  # parent_ts >= this_ts → fail\n" ++
  "  li a0, 0\n" ++
  "  ret\n" ++
  ".Lvhb_fail_gas:\n" ++
  "  li a0, 1\n" ++
  "  ret\n" ++
  ".Lvhb_fail_number:\n" ++
  "  li a0, 2\n" ++
  "  ret\n" ++
  ".Lvhb_fail_timestamp:\n" ++
  "  li a0, 3\n" ++
  "  ret"

/-- `zisk_validate_header_basic`: probe BuildUnit. Reads two
    128-byte extended-header structs from host input (after an
    8-byte tag) and writes the 8-byte status to OUTPUT. -/
def ziskValidateHeaderBasicPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  # Input layout: [pad u64][header 128B][parent 128B]\n" ++
  "  addi a0, a3, 8              # header_ptr\n" ++
  "  addi a1, a3, 136            # parent_ptr (8 + 128)\n" ++
  "  jal ra, validate_header_basic\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lvhb_pdone\n" ++
  validateHeaderBasicFunction ++ "\n" ++
  ".Lvhb_pdone:"

def ziskValidateHeaderBasicDataSection : String :=
  ".section .data\n" ++
  "vhb_pad:\n" ++
  "  .zero 8"

def ziskValidateHeaderBasicProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskValidateHeaderBasicPrologue
  dataAsm     := ziskValidateHeaderBasicDataSection
}

/-! ## check_gas_limit -- PR-K72 gas-limit continuity check

    Verify the per-header gas-limit elasticity rules per
    Ethereum's `check_gas_limit`:

      max_adjustment_delta = parent_gas_limit // 1024
      |gas_limit - parent_gas_limit| < max_adjustment_delta
      gas_limit >= GAS_LIMIT_MINIMUM (5000)

    Used by `validate_header` to ensure consecutive blocks
    smoothly adjust their gas-limit ceiling. Adoption is
    EIP-1985 + EIP-1559 elasticity.

    Pure u64 arithmetic (shift, sub, compare). No scratch
    memory, leaf-callable.

    Calling convention:
      a0 (input)  : new.gas_limit    (u64)
      a1 (input)  : parent.gas_limit (u64)
      ra (input)  : return
      a0 (output) :
        0  : all checks pass
        1  : new.gas_limit < GAS_LIMIT_MINIMUM (5000)
        2  : |new - parent| >= parent / 1024 (jumped too far) -/
def checkGasLimitFunction : String :=
  "check_gas_limit:\n" ++
  "  li t0, 5000                 # GAS_LIMIT_MINIMUM\n" ++
  "  bltu a0, t0, .Lcgl_fail_min\n" ++
  "  # max_adjustment_delta = parent_gas_limit >> 10  (== /1024)\n" ++
  "  srli t1, a1, 10\n" ++
  "  # abs_diff = |new - parent|\n" ++
  "  bgtu a0, a1, .Lcgl_pos\n" ++
  "  sub t2, a1, a0\n" ++
  "  j .Lcgl_check\n" ++
  ".Lcgl_pos:\n" ++
  "  sub t2, a0, a1\n" ++
  ".Lcgl_check:\n" ++
  "  bgeu t2, t1, .Lcgl_fail_jump\n" ++
  "  li a0, 0\n" ++
  "  ret\n" ++
  ".Lcgl_fail_min:\n" ++
  "  li a0, 1\n" ++
  "  ret\n" ++
  ".Lcgl_fail_jump:\n" ++
  "  li a0, 2\n" ++
  "  ret"

/-- `zisk_check_gas_limit`: probe BuildUnit. Reads (new_limit,
    parent_limit) as 2 u64s from host input, writes 8-byte
    status to OUTPUT. -/
def ziskCheckGasLimitPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t0, 0x40000000\n" ++
  "  ld a0,  8(t0)               # new.gas_limit\n" ++
  "  ld a1, 16(t0)               # parent.gas_limit\n" ++
  "  jal ra, check_gas_limit\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lcgl_pdone\n" ++
  checkGasLimitFunction ++ "\n" ++
  ".Lcgl_pdone:"

def ziskCheckGasLimitDataSection : String :=
  ".section .data\n" ++
  "cgl_pad:\n" ++
  "  .zero 8"

def ziskCheckGasLimitProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskCheckGasLimitPrologue
  dataAsm     := ziskCheckGasLimitDataSection
}

/-! ## K69 tx_validate_against_block — moved to `Programs/Tx.lean` (file-size hard cap). -/

/-! ## calc_excess_blob_gas -- PR-K63 EIP-4844 excess blob gas formula

    Compute the next header's `excess_blob_gas` field from the
    parent header. Python (`forks/cancun/fork.py::
    calculate_excess_blob_gas`):

      def calculate_excess_blob_gas(parent_header):
          excess_blob_gas = (
              parent_header.excess_blob_gas
              + parent_header.blob_gas_used
          )
          if excess_blob_gas < TARGET_BLOB_GAS_PER_BLOCK:
              return 0
          return excess_blob_gas - TARGET_BLOB_GAS_PER_BLOCK

    Equivalent to: `max(0, parent.excess_blob_gas +
    parent.blob_gas_used - target)`.

    Used by `validate_header` to check that
    `header.excess_blob_gas == calc_excess_blob_gas(parent,
    target)`.

    The `target` is parameterized — Cancun uses 3 blobs × 131072
    bytes = 393216; Prague/Amsterdam may use a higher target via
    EIP-7691 (e.g. 6 blobs × 131072 = 786432). The function takes
    `target` as an explicit u64 input so it works across forks.

    ## Precondition

    `parent_excess + parent_blob_used` must not overflow u64. In
    practice both terms are small (each < 2^30 on mainnet), so
    overflow doesn't occur. The function does NOT check.

    Calling convention:
      a0 (input)  : parent.excess_blob_gas (u64)
      a1 (input)  : parent.blob_gas_used (u64)
      a2 (input)  : target_blob_gas_per_block (u64)
      ra (input)  : return
      a0 (output) : excess_blob_gas for this header (u64).

    Pure register arithmetic, no scratch memory, leaf-callable. -/
def calcExcessBlobGasFunction : String :=
  "calc_excess_blob_gas:\n" ++
  "  add t0, a0, a1              # parent_excess + parent_used\n" ++
  "  bgeu t0, a2, .Lcebg_pos     # >= target → return diff\n" ++
  "  li a0, 0\n" ++
  "  ret\n" ++
  ".Lcebg_pos:\n" ++
  "  sub a0, t0, a2\n" ++
  "  ret"

/-- `zisk_calc_excess_blob_gas`: probe BuildUnit. Reads
    (parent_excess, parent_used, target) from host input, writes
    the u64 result to OUTPUT. -/
def ziskCalcExcessBlobGasPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a0, 8(a3)                # parent_excess_blob_gas\n" ++
  "  ld a1, 16(a3)               # parent_blob_gas_used\n" ++
  "  ld a2, 24(a3)               # target_blob_gas_per_block\n" ++
  "  jal ra, calc_excess_blob_gas\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lcebg_pdone\n" ++
  calcExcessBlobGasFunction ++ "\n" ++
  ".Lcebg_pdone:"

def ziskCalcExcessBlobGasDataSection : String :=
  ".section .data\n" ++
  "cebg_pad:\n" ++
  "  .zero 8"

def ziskCalcExcessBlobGasProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskCalcExcessBlobGasPrologue
  dataAsm     := ziskCalcExcessBlobGasDataSection
}

/-! ## header_validate_post_merge -- PR-K67

    Verify the three post-merge header invariants:

      1. header.ommers_hash == EMPTY_OMMERS_HASH
         (= keccak256(rlp([])) = 0x1dcc4de8...49347)
      2. header.difficulty == 0   (canonical RLP: empty-string,
                                   content_length == 0)
      3. header.nonce == 0x0000000000000000   (8 zero bytes)

    Mirrors the Python `validate_header` checks added at the
    Merge fork:

      assert header.ommers_hash == EMPTY_OMMERS_HASH
      assert header.difficulty == 0
      assert header.nonce == b"\\x00" * 8

    Composes PR-K20 `rlp_list_nth_item` for field extraction.
    Each check has a distinct return code so callers can pinpoint
    which invariant failed.

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp byte length
      ra (input)  : return
      a0 (output) :
        0  : all three invariants hold
        1  : ommers_hash mismatch
        2  : difficulty != 0
        3  : nonce not 8 zero bytes
        4  : RLP parse failure (e.g. not a list, field missing)

    Uses 40 bytes of `.data` scratch (`hvpm_off`, `hvpm_len`
    + 32-byte `empty_ommers_hash` constant). -/
def headerValidatePostMergeFunction : String :=
  "header_validate_post_merge:\n" ++
  "  addi sp, sp, -24\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp)\n" ++
  "  mv s0, a0                   # header ptr\n" ++
  "  mv s1, a1                   # header_len\n" ++
  "  # Check 1: field 1 (ommers_hash) == EMPTY_OMMERS_HASH.\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 1\n" ++
  "  la a3, hvpm_off; la a4, hvpm_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lhvpm_fail_parse\n" ++
  "  la t0, hvpm_len; ld t1, 0(t0)\n" ++
  "  li t2, 32\n" ++
  "  bne t1, t2, .Lhvpm_fail_oh\n" ++
  "  la t0, hvpm_off; ld t3, 0(t0); add t3, s0, t3\n" ++
  "  la t4, empty_ommers_hash\n" ++
  "  ld t5,  0(t3); ld t6,  0(t4); bne t5, t6, .Lhvpm_fail_oh\n" ++
  "  ld t5,  8(t3); ld t6,  8(t4); bne t5, t6, .Lhvpm_fail_oh\n" ++
  "  ld t5, 16(t3); ld t6, 16(t4); bne t5, t6, .Lhvpm_fail_oh\n" ++
  "  ld t5, 24(t3); ld t6, 24(t4); bne t5, t6, .Lhvpm_fail_oh\n" ++
  "  # Check 2: field 7 (difficulty) is canonical-zero (len 0).\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 7\n" ++
  "  la a3, hvpm_off; la a4, hvpm_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lhvpm_fail_parse\n" ++
  "  la t0, hvpm_len; ld t1, 0(t0)\n" ++
  "  bnez t1, .Lhvpm_fail_diff\n" ++
  "  # Check 3: field 14 (nonce) is 8 zero bytes.\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 14\n" ++
  "  la a3, hvpm_off; la a4, hvpm_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lhvpm_fail_parse\n" ++
  "  la t0, hvpm_len; ld t1, 0(t0)\n" ++
  "  li t2, 8\n" ++
  "  bne t1, t2, .Lhvpm_fail_nonce\n" ++
  "  la t0, hvpm_off; ld t3, 0(t0); add t3, s0, t3\n" ++
  "  ld t5, 0(t3)\n" ++
  "  bnez t5, .Lhvpm_fail_nonce\n" ++
  "  li a0, 0\n" ++
  "  j .Lhvpm_ret\n" ++
  ".Lhvpm_fail_oh:\n" ++
  "  li a0, 1\n" ++
  "  j .Lhvpm_ret\n" ++
  ".Lhvpm_fail_diff:\n" ++
  "  li a0, 2\n" ++
  "  j .Lhvpm_ret\n" ++
  ".Lhvpm_fail_nonce:\n" ++
  "  li a0, 3\n" ++
  "  j .Lhvpm_ret\n" ++
  ".Lhvpm_fail_parse:\n" ++
  "  li a0, 4\n" ++
  ".Lhvpm_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp)\n" ++
  "  addi sp, sp, 24\n" ++
  "  ret"

/-- `zisk_header_validate_post_merge`: probe BuildUnit. Reads
    (header_len, header_bytes) from host input, writes 8-byte
    status to OUTPUT. -/
def ziskHeaderValidatePostMergePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # header_len\n" ++
  "  addi a0, a3, 16             # header ptr\n" ++
  "  jal ra, header_validate_post_merge\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lhvpm_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  headerValidatePostMergeFunction ++ "\n" ++
  ".Lhvpm_pdone:"

def ziskHeaderValidatePostMergeDataSection : String :=
  ".section .data\n" ++
  ".balign 32\n" ++
  "empty_ommers_hash:\n" ++
  "  .byte 0x1d, 0xcc, 0x4d, 0xe8, 0xde, 0xc7, 0x5d, 0x7a\n" ++
  "  .byte 0xab, 0x85, 0xb5, 0x67, 0xb6, 0xcc, 0xd4, 0x1a\n" ++
  "  .byte 0xd3, 0x12, 0x45, 0x1b, 0x94, 0x8a, 0x74, 0x13\n" ++
  "  .byte 0xf0, 0xa1, 0x42, 0xfd, 0x40, 0xd4, 0x93, 0x47\n" ++
  ".balign 8\n" ++
  "hvpm_off:\n" ++
  "  .zero 8\n" ++
  "hvpm_len:\n" ++
  "  .zero 8"

def ziskHeaderValidatePostMergeProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskHeaderValidatePostMergePrologue
  dataAsm     := ziskHeaderValidatePostMergeDataSection
}


/-! ## header_validate_extra_data_length -- PR-K68

    Verify the Ethereum spec constraint that `header.extra_data`
    is at most 32 bytes (Yellow Paper §4.4.4).

    Mirrors the Python check in `validate_header`:

      assert len(header.extra_data) <= 32

    Composes PR-K20 `rlp_list_nth_item` to extract field 12
    (extra_data) and a single u64 compare.

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp byte length
      ra (input)  : return
      a0 (output) :
        0  : extra_data length ≤ 32 bytes
        1  : extra_data length > 32 bytes (reject)
        2  : RLP parse failure (e.g. not a list, field missing)

    Uses two 8-byte `.data` scratch slots (`hved_off`,
    `hved_len`). -/
def headerValidateExtraDataLengthFunction : String :=
  "header_validate_extra_data_length:\n" ++
  "  addi sp, sp, -16\n" ++
  "  sd ra,  0(sp)\n" ++
  "  li a2, 12\n" ++
  "  la a3, hved_off\n" ++
  "  la a4, hved_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lhved_parse_fail\n" ++
  "  la t0, hved_len; ld t1, 0(t0)\n" ++
  "  li t2, 32\n" ++
  "  bgtu t1, t2, .Lhved_too_long\n" ++
  "  li a0, 0\n" ++
  "  j .Lhved_ret\n" ++
  ".Lhved_too_long:\n" ++
  "  li a0, 1\n" ++
  "  j .Lhved_ret\n" ++
  ".Lhved_parse_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lhved_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  addi sp, sp, 16\n" ++
  "  ret"

/-- `zisk_header_validate_extra_data_length`: probe BuildUnit.
    Reads (header_len, header_bytes), writes 8-byte status. -/
def ziskHeaderValidateExtraDataLengthPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  ld a1, 8(a3)                # header_len\n" ++
  "  addi a0, a3, 16             # header ptr\n" ++
  "  jal ra, header_validate_extra_data_length\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lhved_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  headerValidateExtraDataLengthFunction ++ "\n" ++
  ".Lhved_pdone:"

def ziskHeaderValidateExtraDataLengthDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "hved_off:\n" ++
  "  .zero 8\n" ++
  "hved_len:\n" ++
  "  .zero 8"

def ziskHeaderValidateExtraDataLengthProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskHeaderValidateExtraDataLengthPrologue
  dataAsm     := ziskHeaderValidateExtraDataLengthDataSection
}


/-! ## u256-BE arithmetic / comparison / pricing helpers (PR-K51/K52/K56/K58/K59/K60/K61/K62/K70/K53/K54)
    Function + probe defs moved to `Programs/Tx.lean` (see file-size hard cap at the bottom of this file). -/

/-! ## account_charge_gas_pre_exec -- PR-K81

    Apply the pre-EVM sender-account mutation per Python's
    `process_transaction`:

      sender.balance -= effective_gas_price * gas_limit
      sender.nonce   += 1

    Mirrors the upfront max-gas-fee withdrawal in Python:

      sender_account.balance -= effective_gas_price * tx.gas
      sender_account.nonce   += 1

    Note: tx.value is NOT deducted here — it's transferred
    internally by the EVM via CALL/CREATE semantics. This helper
    only handles the gas-fee deduction + nonce bump.

    Post-execution, the caller refunds unused gas via:

      sender.balance += remaining_gas * effective_gas_price

    Composes:
      - PR-K54 `u256_mul_u64_be` — compute gas_fee
      - PR-K52 `u256_sub_be`     — deduct from balance

    The caller passes the current nonce via an in-out `nonce_ptr`
    (u64); this helper reads it, then writes back `nonce + 1`.
    The balance is modified in place.

    Calling convention:
      a0 (input)  : balance ptr (32 B u256 BE; modified in place)
      a1 (input)  : effective_gas_price ptr (32 B u256 BE)
      a2 (input)  : gas_limit (u64)
      a3 (input)  : nonce ptr (u64; in-out; receives nonce+1)
      ra (input)  : return
      a0 (output) :
        0  : success — balance reduced, nonce incremented
        1  : gas_fee computation overflowed u256
        2  : balance < gas_fee (caller should have already
             rejected via PR-K79 `validate_transaction_balance`,
             but the underflow is reported as a safety net)

    Uses 32 bytes of `.data` scratch (`acpg_gas_fee`) plus the
    40-byte `u256m_acc` scratch from PR-K54. -/
def accountChargeGasPreExecFunction : String :=
  "account_charge_gas_pre_exec:\n" ++
  "  addi sp, sp, -24\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp)\n" ++
  "  mv s0, a0                   # balance ptr\n" ++
  "  mv s1, a3                   # nonce ptr (in-out)\n" ++
  "  # gas_fee = effective_gas_price × gas_limit\n" ++
  "  mv a0, a1\n" ++
  "  mv a1, a2\n" ++
  "  la a2, acpg_gas_fee\n" ++
  "  jal ra, u256_mul_u64_be\n" ++
  "  bnez a0, .Lacpg_fail_mul\n" ++
  "  # balance -= gas_fee\n" ++
  "  mv a0, s0\n" ++
  "  la a1, acpg_gas_fee\n" ++
  "  mv a2, s0\n" ++
  "  jal ra, u256_sub_be\n" ++
  "  bnez a0, .Lacpg_fail_sub\n" ++
  "  # *nonce_ptr += 1\n" ++
  "  ld t0, 0(s1)\n" ++
  "  addi t0, t0, 1\n" ++
  "  sd t0, 0(s1)\n" ++
  "  li a0, 0\n" ++
  "  j .Lacpg_ret\n" ++
  ".Lacpg_fail_mul:\n" ++
  "  li a0, 1\n" ++
  "  j .Lacpg_ret\n" ++
  ".Lacpg_fail_sub:\n" ++
  "  li a0, 2\n" ++
  ".Lacpg_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp)\n" ++
  "  addi sp, sp, 24\n" ++
  "  ret"

/-- `zisk_account_charge_gas_pre_exec`: probe BuildUnit. Reads
    (32B balance, 32B egp, 8B gas_limit LE, 8B nonce LE) from
    host input; copies them into OUTPUT-resident buffers; calls
    the helper; writes (status, new_balance, new_nonce) to
    OUTPUT (8 + 32 + 8 = 48 bytes). -/
def ziskAccountChargeGasPreExecPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a4, 0x40000000\n" ++
  "  # Copy balance to OUTPUT + 8 (in-place mutation target)\n" ++
  "  li a0, 0xa0010008\n" ++
  "  addi t1, a4, 8\n" ++
  "  ld t2,  0(t1); sd t2,  0(a0)\n" ++
  "  ld t2,  8(t1); sd t2,  8(a0)\n" ++
  "  ld t2, 16(t1); sd t2, 16(a0)\n" ++
  "  ld t2, 24(t1); sd t2, 24(a0)\n" ++
  "  # egp ptr → input region\n" ++
  "  addi a1, a4, 40             # egp ptr at file offset 32\n" ++
  "  ld a2, 72(a4)               # gas_limit\n" ++
  "  # Copy nonce to OUTPUT + 40 (8 B in-out scratch)\n" ++
  "  li a3, 0xa0010028\n" ++
  "  ld t2, 80(a4)\n" ++
  "  sd t2, 0(a3)\n" ++
  "  jal ra, account_charge_gas_pre_exec\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lacpg_pdone\n" ++
  u256MulU64BeFunction ++ "\n" ++
  u256SubBeFunction ++ "\n" ++
  accountChargeGasPreExecFunction ++ "\n" ++
  ".Lacpg_pdone:"

def ziskAccountChargeGasPreExecDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "u256m_acc:\n" ++
  "  .zero 40\n" ++
  ".balign 32\n" ++
  "acpg_gas_fee:\n" ++
  "  .zero 32"

def ziskAccountChargeGasPreExecProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskAccountChargeGasPreExecPrologue
  dataAsm     := ziskAccountChargeGasPreExecDataSection
}

/-! ## account_refund_gas_post_exec -- PR-K82

    Apply the post-EVM gas accounting mutations per Python's
    `process_transaction`:

      gas_refund    = remaining_gas * effective_gas_price
      sender.balance   += gas_refund
      priority_credit  = gas_used * priority_fee_per_gas
      coinbase.balance += priority_credit

    Where `priority_fee_per_gas = effective_gas_price - base_fee_per_gas`
    (the pre-computed result from PR-K62
    `priority_fee_per_gas_eip1559`).

    Sister to PR-K81 `account_charge_gas_pre_exec`. Together they
    bracket `execute_message`:

      pre:  K81 → sender.balance -= max_gas_fee; sender.nonce++
      ...   EVM run
      post: K82 → sender.balance += gas_refund;
                 coinbase.balance += priority_credit

    Composes:
      - PR-K54 `u256_mul_u64_be` × 2 (sender_refund + coinbase_credit)
      - PR-K51 `u256_add_be` × 2

    Calling convention:
      a0 (input)  : sender.balance ptr (32 B u256 BE; mod in place)
      a1 (input)  : coinbase.balance ptr (32 B u256 BE; mod in place)
      a2 (input)  : effective_gas_price ptr (32 B u256 BE)
      a3 (input)  : priority_fee_per_gas ptr (32 B u256 BE)
      a4 (input)  : gas_used (u64)
      a5 (input)  : remaining_gas (u64)
      ra (input)  : return
      a0 (output) :
        0  : success — both balances updated
        1  : mul overflow on refund or credit
        2  : add overflow on either balance

    Uses 64 bytes of `.data` scratch (`arg_sender_refund` +
    `arg_coinbase_credit`) plus the 40-byte `u256m_acc`. -/
def accountRefundGasPostExecFunction : String :=
  "account_refund_gas_post_exec:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0                   # sender ptr\n" ++
  "  mv s1, a1                   # coinbase ptr\n" ++
  "  mv s2, a3                   # priority_fee ptr (saved for step 2)\n" ++
  "  mv s3, a4                   # gas_used (saved for step 2)\n" ++
  "  mv s4, a2                   # egp ptr (also saved; step 1 uses)\n" ++
  "  # Step 1: sender_refund = remaining_gas × egp\n" ++
  "  mv a0, s4\n" ++
  "  mv a1, a5\n" ++
  "  la a2, arg_sender_refund\n" ++
  "  jal ra, u256_mul_u64_be\n" ++
  "  bnez a0, .Largpe_fail_mul\n" ++
  "  # Step 2: coinbase_credit = gas_used × priority_fee\n" ++
  "  mv a0, s2\n" ++
  "  mv a1, s3\n" ++
  "  la a2, arg_coinbase_credit\n" ++
  "  jal ra, u256_mul_u64_be\n" ++
  "  bnez a0, .Largpe_fail_mul\n" ++
  "  # Step 3: sender.balance += sender_refund\n" ++
  "  mv a0, s0\n" ++
  "  la a1, arg_sender_refund\n" ++
  "  mv a2, s0\n" ++
  "  jal ra, u256_add_be\n" ++
  "  bnez a0, .Largpe_fail_add\n" ++
  "  # Step 4: coinbase.balance += coinbase_credit\n" ++
  "  mv a0, s1\n" ++
  "  la a1, arg_coinbase_credit\n" ++
  "  mv a2, s1\n" ++
  "  jal ra, u256_add_be\n" ++
  "  bnez a0, .Largpe_fail_add\n" ++
  "  li a0, 0\n" ++
  "  j .Largpe_ret\n" ++
  ".Largpe_fail_mul:\n" ++
  "  li a0, 1\n" ++
  "  j .Largpe_ret\n" ++
  ".Largpe_fail_add:\n" ++
  "  li a0, 2\n" ++
  ".Largpe_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- `zisk_account_refund_gas_post_exec`: probe BuildUnit. Reads
    (32B sender_bal, 32B coinbase_bal, 32B egp, 32B priority_fee,
    8B gas_used, 8B remaining_gas) from host input. Copies the
    two balances to OUTPUT-resident scratch buffers, calls the
    helper, then writes (status, new_sender, new_coinbase) to
    OUTPUT. Total OUTPUT bytes: 8 + 32 + 32 = 72. -/
def ziskAccountRefundGasPostExecPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a6, 0x40000000\n" ++
  "  # Copy sender balance to OUTPUT + 8\n" ++
  "  li a0, 0xa0010008\n" ++
  "  addi t1, a6, 8\n" ++
  "  ld t2,  0(t1); sd t2,  0(a0)\n" ++
  "  ld t2,  8(t1); sd t2,  8(a0)\n" ++
  "  ld t2, 16(t1); sd t2, 16(a0)\n" ++
  "  ld t2, 24(t1); sd t2, 24(a0)\n" ++
  "  # Copy coinbase balance to OUTPUT + 40\n" ++
  "  li a1, 0xa0010028\n" ++
  "  addi t1, a6, 40\n" ++
  "  ld t2,  0(t1); sd t2,  0(a1)\n" ++
  "  ld t2,  8(t1); sd t2,  8(a1)\n" ++
  "  ld t2, 16(t1); sd t2, 16(a1)\n" ++
  "  ld t2, 24(t1); sd t2, 24(a1)\n" ++
  "  addi a2, a6, 72             # egp ptr\n" ++
  "  addi a3, a6, 104            # priority_fee ptr\n" ++
  "  ld a4, 136(a6)              # gas_used\n" ++
  "  ld a5, 144(a6)              # remaining_gas\n" ++
  "  jal ra, account_refund_gas_post_exec\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Largpe_pdone\n" ++
  u256MulU64BeFunction ++ "\n" ++
  u256AddBeFunction ++ "\n" ++
  accountRefundGasPostExecFunction ++ "\n" ++
  ".Largpe_pdone:"

def ziskAccountRefundGasPostExecDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "u256m_acc:\n" ++
  "  .zero 40\n" ++
  ".balign 32\n" ++
  "arg_sender_refund:\n" ++
  "  .zero 32\n" ++
  ".balign 32\n" ++
  "arg_coinbase_credit:\n" ++
  "  .zero 32"

def ziskAccountRefundGasPostExecProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskAccountRefundGasPostExecPrologue
  dataAsm     := ziskAccountRefundGasPostExecDataSection
}

/-! ## eip1559_calc_base_fee_per_gas -- PR-K73

    Full EIP-1559 base-fee formula. Mirrors Python's
    `calculate_base_fee_per_gas`:

      parent_gas_target = parent.gas_limit // 2

      if parent.gas_used == parent_gas_target:
          expected = parent.base_fee_per_gas
      elif parent.gas_used > parent_gas_target:
          gas_used_delta = parent.gas_used - parent_gas_target
          parent_fee_gas_delta = parent.base_fee_per_gas * gas_used_delta
          target_fee_gas_delta = parent_fee_gas_delta // parent_gas_target
          base_fee_delta = max(target_fee_gas_delta // 8, 1)
          expected = parent.base_fee_per_gas + base_fee_delta
      else:
          gas_used_delta = parent_gas_target - parent.gas_used
          parent_fee_gas_delta = parent.base_fee_per_gas * gas_used_delta
          target_fee_gas_delta = parent_fee_gas_delta // parent_gas_target
          base_fee_delta = target_fee_gas_delta // 8
          expected = parent.base_fee_per_gas - base_fee_delta

    Where `ELASTICITY_MULTIPLIER = 2` and
    `BASE_FEE_MAX_CHANGE_DENOMINATOR = 8`.

    First end-to-end EIP-1559 helper composed on the u256 toolkit:
    - PR-K54 `u256_mul_u64_be` — parent.base_fee × gas_used_delta
    - PR-K61 `u256_div_u64_be` — divide by parent_gas_target, then by 8
    - PR-K58 `u256_is_zero`    — max(_, 1) on the above path
    - PR-K56 `u256_from_u64_be` — materialize the literal 1
    - PR-K51 `u256_add_be`     — final add (above path)
    - PR-K52 `u256_sub_be`     — final sub (below path)

    ## Preconditions

    - `parent.gas_limit >= 2` (so `parent_gas_target >= 1`; we
      divide by it). Mainnet has GAS_LIMIT_MINIMUM = 5000, so
      this always holds for valid chains.
    - `parent.base_fee_per_gas <= 2^56` (PR-K61 div precondition).
      All mainnet base fees fit easily.

    Calling convention:
      a0 (input)  : parent.gas_limit       (u64)
      a1 (input)  : parent.gas_used        (u64)
      a2 (input)  : parent.base_fee_per_gas ptr (u256 BE, 32 B)
      a3 (input)  : output ptr (u256 BE, 32 B; receives expected
                    base_fee_per_gas)
      ra (input)  : return
      a0 (output) : 0 on success, 1 on overflow at any step. -/
def eip1559CalcBaseFeePerGasFunction : String :=
  "eip1559_calc_base_fee_per_gas:\n" ++
  "  addi sp, sp, -56\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a2                    # base_fee ptr\n" ++
  "  mv s1, a3                    # out ptr\n" ++
  "  srli s2, a0, 1               # parent_gas_target = parent.gas_limit / 2\n" ++
  "  beq a1, s2, .Lebf_eq         # gas_used == target → expected = base_fee\n" ++
  "  li s4, 0                     # path flag: 0 = below, 1 = above\n" ++
  "  bgtu a1, s2, .Lebf_set_above\n" ++
  "  sub s3, s2, a1               # below: delta = target - gas_used\n" ++
  "  j .Lebf_compute\n" ++
  ".Lebf_set_above:\n" ++
  "  li s4, 1\n" ++
  "  sub s3, a1, s2               # above: delta = gas_used - target\n" ++
  ".Lebf_compute:\n" ++
  "  # parent_fee_gas_delta = parent.base_fee × gas_used_delta\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s3\n" ++
  "  mv a2, s1\n" ++
  "  jal ra, u256_mul_u64_be\n" ++
  "  bnez a0, .Lebf_fail\n" ++
  "  # target_fee_gas_delta = parent_fee_gas_delta / parent_gas_target\n" ++
  "  mv a0, s1\n" ++
  "  mv a1, s2\n" ++
  "  mv a2, s1\n" ++
  "  jal ra, u256_div_u64_be\n" ++
  "  # base_fee_delta = target_fee_gas_delta / 8\n" ++
  "  mv a0, s1\n" ++
  "  li a1, 8\n" ++
  "  mv a2, s1\n" ++
  "  jal ra, u256_div_u64_be\n" ++
  "  # If above path: max(delta, 1).\n" ++
  "  beqz s4, .Lebf_apply\n" ++
  "  mv a0, s1\n" ++
  "  jal ra, u256_is_zero\n" ++
  "  beqz a0, .Lebf_apply\n" ++
  "  li a0, 1\n" ++
  "  mv a1, s1\n" ++
  "  jal ra, u256_from_u64_be\n" ++
  ".Lebf_apply:\n" ++
  "  beqz s4, .Lebf_sub_path\n" ++
  "  # above: out = base_fee + delta\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s1\n" ++
  "  mv a2, s1\n" ++
  "  jal ra, u256_add_be\n" ++
  "  bnez a0, .Lebf_fail\n" ++
  "  li a0, 0\n" ++
  "  j .Lebf_ret\n" ++
  ".Lebf_sub_path:\n" ++
  "  # below: out = base_fee - delta\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s1\n" ++
  "  mv a2, s1\n" ++
  "  jal ra, u256_sub_be\n" ++
  "  bnez a0, .Lebf_fail\n" ++
  "  li a0, 0\n" ++
  "  j .Lebf_ret\n" ++
  ".Lebf_eq:\n" ++
  "  # Copy base_fee to out (32 B chunk copy).\n" ++
  "  ld t0,  0(s0); sd t0,  0(s1)\n" ++
  "  ld t0,  8(s0); sd t0,  8(s1)\n" ++
  "  ld t0, 16(s0); sd t0, 16(s1)\n" ++
  "  ld t0, 24(s0); sd t0, 24(s1)\n" ++
  "  li a0, 0\n" ++
  "  j .Lebf_ret\n" ++
  ".Lebf_fail:\n" ++
  "  li a0, 1\n" ++
  ".Lebf_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 56\n" ++
  "  ret"

/-- `zisk_eip1559_calc_base_fee_per_gas`: probe BuildUnit. Reads
    (parent_gas_limit u64, parent_gas_used u64, parent_base_fee
    u256 BE) from host input, writes (status, expected_base_fee
    BE) to OUTPUT (40 bytes total). -/
def ziskEip1559CalcBaseFeePerGasPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a4, 0x40000000\n" ++
  "  ld a0,  8(a4)               # parent.gas_limit\n" ++
  "  ld a1, 16(a4)               # parent.gas_used\n" ++
  "  addi a2, a4, 24             # parent.base_fee ptr\n" ++
  "  li a3, 0xa0010008           # out ptr\n" ++
  "  mv t0, a3; li t1, 4\n" ++
  ".Lebf_zout:\n" ++
  "  beqz t1, .Lebf_zout_done\n" ++
  "  sd zero, 0(t0)\n" ++
  "  addi t0, t0, 8\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Lebf_zout\n" ++
  ".Lebf_zout_done:\n" ++
  "  jal ra, eip1559_calc_base_fee_per_gas\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lebf_pdone\n" ++
  u256MulU64BeFunction ++ "\n" ++
  u256DivU64BeFunction ++ "\n" ++
  u256IsZeroFunction ++ "\n" ++
  u256FromU64BeFunction ++ "\n" ++
  u256AddBeFunction ++ "\n" ++
  u256SubBeFunction ++ "\n" ++
  eip1559CalcBaseFeePerGasFunction ++ "\n" ++
  ".Lebf_pdone:"

def ziskEip1559CalcBaseFeePerGasDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "u256m_acc:\n" ++
  "  .zero 40"

def ziskEip1559CalcBaseFeePerGasProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskEip1559CalcBaseFeePerGasPrologue
  dataAsm     := ziskEip1559CalcBaseFeePerGasDataSection
}

/-! ## header_validate_base_fee -- PR-K74

    Verify a header's `base_fee_per_gas` matches the value
    computed from the parent header by EIP-1559's
    `calculate_base_fee_per_gas`:

      expected = eip1559_calc_base_fee_per_gas(
                   parent.gas_limit,
                   parent.gas_used,
                   parent.base_fee_per_gas)
      assert header.base_fee_per_gas == expected

    This is the per-block invariant added by EIP-1559 §4.4.4
    (Python: `validate_header`).

    Composes PR-K73 `eip1559_calc_base_fee_per_gas` +
    PR-K53 `u256_eq`. The 32-byte computed expected base fee
    lands in `.data` scratch, then is compared bytewise against
    the header's claimed value.

    Calling convention:
      a0 (input)  : header.base_fee_per_gas ptr (u256 BE, 32 B)
      a1 (input)  : parent.gas_limit (u64)
      a2 (input)  : parent.gas_used (u64)
      a3 (input)  : parent.base_fee_per_gas ptr (u256 BE, 32 B)
      ra (input)  : return
      a0 (output) :
        0  : header.base_fee_per_gas == expected
        1  : mismatch (reject)
        2  : compute step (K73) overflow / precondition failure

    Uses 32 bytes of `.data` scratch (`hvbf_expected`). -/
def headerValidateBaseFeeFunction : String :=
  "header_validate_base_fee:\n" ++
  "  addi sp, sp, -16\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp)\n" ++
  "  mv s0, a0                   # save header.base_fee ptr\n" ++
  "  # expected = eip1559_calc_base_fee_per_gas(...)  → hvbf_expected\n" ++
  "  mv a0, a1                   # parent.gas_limit\n" ++
  "  mv a1, a2                   # parent.gas_used\n" ++
  "  mv a2, a3                   # parent.base_fee\n" ++
  "  la a3, hvbf_expected\n" ++
  "  jal ra, eip1559_calc_base_fee_per_gas\n" ++
  "  bnez a0, .Lhvbf_fail_compute\n" ++
  "  # Compare header.base_fee vs expected.\n" ++
  "  mv a0, s0\n" ++
  "  la a1, hvbf_expected\n" ++
  "  jal ra, u256_eq             # a0 = 1 if equal, 0 if not\n" ++
  "  beqz a0, .Lhvbf_fail_mismatch\n" ++
  "  li a0, 0\n" ++
  "  j .Lhvbf_ret\n" ++
  ".Lhvbf_fail_mismatch:\n" ++
  "  li a0, 1\n" ++
  "  j .Lhvbf_ret\n" ++
  ".Lhvbf_fail_compute:\n" ++
  "  li a0, 2\n" ++
  ".Lhvbf_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp)\n" ++
  "  addi sp, sp, 16\n" ++
  "  ret"

/-- `zisk_header_validate_base_fee`: probe BuildUnit. Reads
    (header_bf u256 BE, parent_gas_limit u64, parent_gas_used u64,
    parent_bf u256 BE) from host input, writes 8-byte status. -/
def ziskHeaderValidateBaseFeePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a4, 0x40000000\n" ++
  "  addi a0, a4, 8              # header_bf ptr\n" ++
  "  ld a1, 40(a4)               # parent.gas_limit\n" ++
  "  ld a2, 48(a4)               # parent.gas_used\n" ++
  "  addi a3, a4, 56             # parent_bf ptr\n" ++
  "  jal ra, header_validate_base_fee\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lhvbf_pdone\n" ++
  u256MulU64BeFunction ++ "\n" ++
  u256DivU64BeFunction ++ "\n" ++
  u256IsZeroFunction ++ "\n" ++
  u256FromU64BeFunction ++ "\n" ++
  u256AddBeFunction ++ "\n" ++
  u256SubBeFunction ++ "\n" ++
  u256EqFunction ++ "\n" ++
  eip1559CalcBaseFeePerGasFunction ++ "\n" ++
  headerValidateBaseFeeFunction ++ "\n" ++
  ".Lhvbf_pdone:"

def ziskHeaderValidateBaseFeeDataSection : String :=
  ".section .data\n" ++
  ".balign 32\n" ++
  "hvbf_expected:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "u256m_acc:\n" ++
  "  .zero 40"

def ziskHeaderValidateBaseFeeProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskHeaderValidateBaseFeePrologue
  dataAsm     := ziskHeaderValidateBaseFeeDataSection
}

/-! ## validate_header_full -- PR-K75 complete per-header validation

    Run all five per-header validation checks in sequence, returning
    a single status code that distinguishes which step failed:

      1. PR-K67 `header_validate_post_merge`        — ommers/difficulty/nonce
      2. PR-K68 `header_validate_extra_data_length` — extra_data ≤ 32 bytes
      3. PR-K43 `validate_header_basic`             — gas_used ≤ gas_limit + number/timestamp
      4. PR-K72 `check_gas_limit`                   — elasticity
      5. PR-K74 `header_validate_base_fee`          — EIP-1559 invariant

    Chain-level checks (parent_hash continuity, validate_chain
    PR-K18) are NOT included here — they iterate across multiple
    headers and live at the SSZ-list walk level.

    Status encoding:

      0                : all five checks pass
      100..104         : step 1 failed with K67's sub-status 0..4
      201..202         : step 2 failed with K68's sub-status 1..2
      301..303         : step 3 failed with K43's sub-status 1..3
      401..402         : step 4 failed with K72's sub-status 1..2
      501..502         : step 5 failed with K74's sub-status 1..2

    Distinct decades let callers `floor(status/100)` to identify
    the failing step.

    Calling convention:
      a0 (input)  : this header's RLP ptr
      a1 (input)  : this header's RLP byte length
      a2 (input)  : this header's PR-K39 extended-decode struct
                    (128 B, with gas_limit @ 80, gas_used @ 88,
                    base_fee_per_gas @ 96..128)
      a3 (input)  : parent header's PR-K39 extended-decode struct
                    (same layout)
      ra (input)  : return
      a0 (output) : composite status (see encoding above).

    Composes 5 validators + their transitive deps (rlp_list_nth_item,
    eip1559_calc_base_fee_per_gas plus the u256 toolkit). The probe
    inlines every function it transitively calls. -/
def validateHeaderFullFunction : String :=
  "validate_header_full:\n" ++
  "  addi sp, sp, -56\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  mv s0, a0                   # this_rlp ptr\n" ++
  "  mv s1, a1                   # this_rlp_len\n" ++
  "  mv s2, a2                   # this_struct (128 B)\n" ++
  "  mv s3, a3                   # parent_struct (128 B)\n" ++
  "  # Step 1: post_merge check\n" ++
  "  mv a0, s0; mv a1, s1\n" ++
  "  jal ra, header_validate_post_merge\n" ++
  "  beqz a0, .Lvhf_s2\n" ++
  "  li t0, 100\n" ++
  "  add a0, a0, t0\n" ++
  "  j .Lvhf_ret\n" ++
  ".Lvhf_s2:\n" ++
  "  # Step 2: extra_data length check\n" ++
  "  mv a0, s0; mv a1, s1\n" ++
  "  jal ra, header_validate_extra_data_length\n" ++
  "  beqz a0, .Lvhf_s3\n" ++
  "  li t0, 200\n" ++
  "  add a0, a0, t0\n" ++
  "  j .Lvhf_ret\n" ++
  ".Lvhf_s3:\n" ++
  "  # Step 3: gas_used/number/timestamp\n" ++
  "  mv a0, s2; mv a1, s3\n" ++
  "  jal ra, validate_header_basic\n" ++
  "  beqz a0, .Lvhf_s4\n" ++
  "  li t0, 300\n" ++
  "  add a0, a0, t0\n" ++
  "  j .Lvhf_ret\n" ++
  ".Lvhf_s4:\n" ++
  "  # Step 4: check_gas_limit(this.gas_limit, parent.gas_limit)\n" ++
  "  ld a0, 80(s2)\n" ++
  "  ld a1, 80(s3)\n" ++
  "  jal ra, check_gas_limit\n" ++
  "  beqz a0, .Lvhf_s5\n" ++
  "  li t0, 400\n" ++
  "  add a0, a0, t0\n" ++
  "  j .Lvhf_ret\n" ++
  ".Lvhf_s5:\n" ++
  "  # Step 5: base_fee continuity\n" ++
  "  addi a0, s2, 96\n" ++
  "  ld a1, 80(s3)\n" ++
  "  ld a2, 88(s3)\n" ++
  "  addi a3, s3, 96\n" ++
  "  jal ra, header_validate_base_fee\n" ++
  "  beqz a0, .Lvhf_ret\n" ++
  "  li t0, 500\n" ++
  "  add a0, a0, t0\n" ++
  ".Lvhf_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  addi sp, sp, 56\n" ++
  "  ret"

/-- `zisk_validate_header_full`: probe BuildUnit. Reads (this_rlp_len,
    this_rlp_bytes [up to 1024 B], this_struct 128 B, parent_struct
    128 B) from host input, writes 8-byte composite status to OUTPUT. -/
def ziskValidateHeaderFullPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a4, 0x40000000\n" ++
  "  ld a1, 8(a4)                # this_rlp_len\n" ++
  "  addi a0, a4, 16             # this_rlp ptr\n" ++
  "  addi a2, a4, 16             # placeholder; reset after rlp\n" ++
  "  # this_struct offset = 16 + rlp_len_aligned\n" ++
  "  # parent_struct offset = this_struct + 128\n" ++
  "  # We require the caller to lay them out at fixed positions:\n" ++
  "  # bytes 8..16  : rlp_len\n" ++
  "  # bytes 16..16+1024 : this_rlp (padded to 1024)\n" ++
  "  # bytes 1040..1168  : this_struct (128 B)\n" ++
  "  # bytes 1168..1296  : parent_struct (128 B)\n" ++
  "  li a2, 0x40000410           # this_struct  (= INPUT_ADDR + 1040)\n" ++
  "  li a3, 0x40000490           # parent_struct (= INPUT_ADDR + 1168)\n" ++
  "  jal ra, validate_header_full\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lvhf_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  u256MulU64BeFunction ++ "\n" ++
  u256DivU64BeFunction ++ "\n" ++
  u256IsZeroFunction ++ "\n" ++
  u256FromU64BeFunction ++ "\n" ++
  u256AddBeFunction ++ "\n" ++
  u256SubBeFunction ++ "\n" ++
  u256EqFunction ++ "\n" ++
  validateHeaderBasicFunction ++ "\n" ++
  checkGasLimitFunction ++ "\n" ++
  headerValidatePostMergeFunction ++ "\n" ++
  headerValidateExtraDataLengthFunction ++ "\n" ++
  eip1559CalcBaseFeePerGasFunction ++ "\n" ++
  headerValidateBaseFeeFunction ++ "\n" ++
  validateHeaderFullFunction ++ "\n" ++
  ".Lvhf_pdone:"

def ziskValidateHeaderFullDataSection : String :=
  ".section .data\n" ++
  ".balign 32\n" ++
  "empty_ommers_hash:\n" ++
  "  .byte 0x1d, 0xcc, 0x4d, 0xe8, 0xde, 0xc7, 0x5d, 0x7a\n" ++
  "  .byte 0xab, 0x85, 0xb5, 0x67, 0xb6, 0xcc, 0xd4, 0x1a\n" ++
  "  .byte 0xd3, 0x12, 0x45, 0x1b, 0x94, 0x8a, 0x74, 0x13\n" ++
  "  .byte 0xf0, 0xa1, 0x42, 0xfd, 0x40, 0xd4, 0x93, 0x47\n" ++
  ".balign 32\n" ++
  "hvbf_expected:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "u256m_acc:\n" ++
  "  .zero 40\n" ++
  ".balign 8\n" ++
  "hvpm_off:\n" ++
  "  .zero 8\n" ++
  "hvpm_len:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "hved_off:\n" ++
  "  .zero 8\n" ++
  "hved_len:\n" ++
  "  .zero 8"

def ziskValidateHeaderFullProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskValidateHeaderFullPrologue
  dataAsm     := ziskValidateHeaderFullDataSection
}

/-! ## block_hash_from_header -- PR-K172

    Compute the block hash of an Ethereum block header:
    `block_hash = keccak256(header_rlp_bytes)`.

    The header RLP is the canonical wire encoding of the
    15-or-16-field header list (parent_hash, ommers_hash,
    beneficiary, state_root, transactions_root, receipts_root,
    logs_bloom, difficulty, number, gas_limit, gas_used,
    timestamp, extra_data, prev_randao, nonce, [base_fee, ...
    withdrawals_root, blob_gas_used, excess_blob_gas,
    parent_beacon_block_root]).

    The block hash is identified by `parent_hash` in the next
    header in the chain, so this primitive is the natural
    building block for `validate_headers` (which walks the
    chain and checks each `header[i].parent_hash ==
    block_hash_from_header(header[i-1])`).

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp byte length
      a2 (input)  : 32-byte output ptr (block_hash lands here)
      ra (input)  : return
      (no output register; result is in memory at `a2`) -/
def blockHashFromHeaderFunction : String :=
  "block_hash_from_header:\n" ++
  "  addi sp, sp, -16\n" ++
  "  sd ra, 0(sp)\n" ++
  "  # zkvm_keccak256(a0=header, a1=len, a2=out)\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  ld ra, 0(sp)\n" ++
  "  addi sp, sp, 16\n" ++
  "  ret"

/-- `zisk_block_hash_from_header`: probe BuildUnit.
    Input layout:
      bytes 0..8  : header_rlp byte length
      bytes 8..   : header_rlp
    Output layout:
      bytes 0..32 : block_hash -/
def ziskBlockHashFromHeaderPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a1, 8(a7)                # header_rlp_len\n" ++
  "  addi a0, a7, 16             # header_rlp ptr\n" ++
  "  li a2, 0xa0010000           # output block_hash ptr (32 B)\n" ++
  "  jal ra, block_hash_from_header\n" ++
  "  j .Lbhfh_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  blockHashFromHeaderFunction ++ "\n" ++
  ".Lbhfh_pdone:"

def ziskBlockHashFromHeaderDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200"

def ziskBlockHashFromHeaderProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBlockHashFromHeaderPrologue
  dataAsm     := ziskBlockHashFromHeaderDataSection
}

/-! ## validate_parent_hash_link -- PR-K173

    Given a parent header (parent_rlp) and a child header
    (child_rlp), verify that
    `child.parent_hash == keccak256(parent_rlp)`.

    This is the per-step check inside `validate_headers`: each
    pair of consecutive headers in the chain must satisfy this
    invariant; the full chain follows by induction.

    Algorithm:
      1. K20 extract field 0 (parent_hash) from child_rlp.
         Verify field length == 32.
      2. K172 `block_hash_from_header(parent_rlp)` ->
         computed_hash.
      3. 32-byte memcmp(claimed, computed).
      4. Write verdict (1 = matches, 0 = mismatch); status
         disambiguates parse vs. size vs. predicate failure.

    Calling convention:
      a0 (input)  : parent_rlp ptr
      a1 (input)  : parent_rlp byte length
      a2 (input)  : child_rlp ptr
      a3 (input)  : child_rlp byte length
      a4 (input)  : u64 out (is_valid: 1 if links, else 0)
      ra (input)  : return
      a0 (output) :
        0 : success -- predicate written
        1 : child RLP parse failure / field 0 missing
        2 : child.parent_hash length != 32 -/
def validateParentHashLinkFunction : String :=
  "validate_parent_hash_link:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0                   # parent_rlp ptr\n" ++
  "  mv s1, a1                   # parent_rlp len\n" ++
  "  mv s2, a2                   # child_rlp ptr\n" ++
  "  mv s3, a3                   # child_rlp len\n" ++
  "  mv s4, a4                   # is_valid out\n" ++
  "  sd zero, 0(s4)\n" ++
  "  # ---- Extract child.parent_hash (field 0) ----\n" ++
  "  mv a0, s2; mv a1, s3; li a2, 0\n" ++
  "  la a3, vphl_offset; la a4, vphl_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lvphl_parse_fail\n" ++
  "  la t0, vphl_length; ld t1, 0(t0)\n" ++
  "  li t2, 32\n" ++
  "  bne t1, t2, .Lvphl_size_fail\n" ++
  "  # Copy claimed parent_hash into vphl_claimed\n" ++
  "  la t0, vphl_offset; ld t1, 0(t0)\n" ++
  "  add t3, s2, t1                              # &child[off]\n" ++
  "  la t4, vphl_claimed\n" ++
  "  ld t5,  0(t3); sd t5,  0(t4)\n" ++
  "  ld t5,  8(t3); sd t5,  8(t4)\n" ++
  "  ld t5, 16(t3); sd t5, 16(t4)\n" ++
  "  ld t5, 24(t3); sd t5, 24(t4)\n" ++
  "  # ---- Compute keccak256(parent_rlp) ----\n" ++
  "  mv a0, s0; mv a1, s1\n" ++
  "  la a2, vphl_computed\n" ++
  "  jal ra, block_hash_from_header\n" ++
  "  # ---- 32-byte compare ----\n" ++
  "  la t0, vphl_claimed\n" ++
  "  la t1, vphl_computed\n" ++
  "  ld t2,  0(t0); ld t3,  0(t1); bne t2, t3, .Lvphl_neq\n" ++
  "  ld t2,  8(t0); ld t3,  8(t1); bne t2, t3, .Lvphl_neq\n" ++
  "  ld t2, 16(t0); ld t3, 16(t1); bne t2, t3, .Lvphl_neq\n" ++
  "  ld t2, 24(t0); ld t3, 24(t1); bne t2, t3, .Lvphl_neq\n" ++
  "  li t0, 1\n" ++
  "  sd t0, 0(s4)\n" ++
  "  li a0, 0\n" ++
  "  j .Lvphl_ret\n" ++
  ".Lvphl_neq:\n" ++
  "  sd zero, 0(s4)\n" ++
  "  li a0, 0\n" ++
  "  j .Lvphl_ret\n" ++
  ".Lvphl_parse_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lvphl_ret\n" ++
  ".Lvphl_size_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lvphl_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- `zisk_validate_parent_hash_link`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : parent_rlp_len
      bytes  8..16 : child_rlp_len
      bytes 16..   : parent_rlp || child_rlp
    Output layout:
      bytes  0.. 8 : status (0=ok, 1=child parse, 2=size fail)
      bytes  8..16 : is_valid (1 if links, else 0) -/
def ziskValidateParentHashLinkPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a1, 8(a7)                # parent_rlp_len\n" ++
  "  ld a3, 16(a7)               # child_rlp_len\n" ++
  "  addi a0, a7, 24             # parent_rlp ptr\n" ++
  "  add a2, a0, a1              # child_rlp ptr = parent_rlp + parent_len\n" ++
  "  li a4, 0xa0010008           # is_valid out\n" ++
  "  jal ra, validate_parent_hash_link\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lvphl_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  zkvmKeccak256Function ++ "\n" ++
  blockHashFromHeaderFunction ++ "\n" ++
  validateParentHashLinkFunction ++ "\n" ++
  ".Lvphl_pdone:"

def ziskValidateParentHashLinkDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "vphl_offset:\n" ++
  "  .zero 8\n" ++
  "vphl_length:\n" ++
  "  .zero 8\n" ++
  "vphl_claimed:\n" ++
  "  .zero 32\n" ++
  "vphl_computed:\n" ++
  "  .zero 32"

def ziskValidateParentHashLinkProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskValidateParentHashLinkPrologue
  dataAsm     := ziskValidateParentHashLinkDataSection
}

/-! ## validate_header_pair -- PR-K174

    Per-step pair validator inside `validate_headers`: given a
    parent header and a child header, verify the four
    invariants the EELS `validate_header` function checks
    between consecutive headers:

      1. child.parent_hash == keccak256(parent_rlp)         (K173)
      2. child.number == parent.number + 1
      3. child.timestamp > parent.timestamp
      4. check_gas_limit(child.gas_limit, parent.gas_limit) == 0
         (gas_limit >= 5000 and |new - parent| < parent/1024)

    Per-header field-shape checks (`validate_header_basic`,
    `validate_header_post_merge`, etc.) live in their own
    helpers; this primitive is the **pair** check only.

    Calling convention:
      a0 (input)  : parent_rlp ptr
      a1 (input)  : parent_rlp byte length
      a2 (input)  : child_rlp ptr
      a3 (input)  : child_rlp byte length
      a4 (input)  : u64 out (is_valid: 1 if all 4 invariants hold)
      ra (input)  : return
      a0 (output) :
        0 : success -- predicate written
        1 : child RLP parse failure
        2 : child.parent_hash length != 32
        3 : parent number/timestamp/gas_limit field parse failure
        4 : child number/timestamp/gas_limit field parse failure -/
def validateHeaderPairFunction : String :=
  "validate_header_pair:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0                   # parent_rlp ptr\n" ++
  "  mv s1, a1                   # parent_rlp len\n" ++
  "  mv s2, a2                   # child_rlp ptr\n" ++
  "  mv s3, a3                   # child_rlp len\n" ++
  "  mv s4, a4                   # is_valid out\n" ++
  "  sd zero, 0(s4)\n" ++
  "  # ---- (1) Parent-hash link ----\n" ++
  "  mv a0, s0; mv a1, s1\n" ++
  "  mv a2, s2; mv a3, s3\n" ++
  "  la a4, vhp_link_valid\n" ++
  "  jal ra, validate_parent_hash_link\n" ++
  "  beqz a0, .Lvhp_link_ok\n" ++
  "  li t0, 1\n" ++
  "  beq a0, t0, .Lvhp_child_parse_fail\n" ++
  "  j .Lvhp_size_fail\n" ++
  ".Lvhp_link_ok:\n" ++
  "  la t0, vhp_link_valid; ld t1, 0(t0)\n" ++
  "  beqz t1, .Lvhp_pred_false\n" ++
  "  # ---- (2/3/4) Extract parent number/timestamp/gas_limit ----\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 8\n" ++
  "  la a3, vhp_parent_number\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lvhp_parent_field_fail\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 11\n" ++
  "  la a3, vhp_parent_timestamp\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lvhp_parent_field_fail\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 9\n" ++
  "  la a3, vhp_parent_gas_limit\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lvhp_parent_field_fail\n" ++
  "  # ---- Extract child number/timestamp/gas_limit ----\n" ++
  "  mv a0, s2; mv a1, s3; li a2, 8\n" ++
  "  la a3, vhp_child_number\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lvhp_child_field_fail\n" ++
  "  mv a0, s2; mv a1, s3; li a2, 11\n" ++
  "  la a3, vhp_child_timestamp\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lvhp_child_field_fail\n" ++
  "  mv a0, s2; mv a1, s3; li a2, 9\n" ++
  "  la a3, vhp_child_gas_limit\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lvhp_child_field_fail\n" ++
  "  # (2) child.number == parent.number + 1\n" ++
  "  la t0, vhp_parent_number; ld t1, 0(t0)\n" ++
  "  la t0, vhp_child_number;  ld t2, 0(t0)\n" ++
  "  addi t1, t1, 1\n" ++
  "  bne t1, t2, .Lvhp_pred_false\n" ++
  "  # (3) child.timestamp > parent.timestamp\n" ++
  "  la t0, vhp_parent_timestamp; ld t1, 0(t0)\n" ++
  "  la t0, vhp_child_timestamp;  ld t2, 0(t0)\n" ++
  "  bgeu t1, t2, .Lvhp_pred_false\n" ++
  "  # (4) check_gas_limit(child, parent) == 0\n" ++
  "  la t0, vhp_child_gas_limit;  ld a0, 0(t0)\n" ++
  "  la t0, vhp_parent_gas_limit; ld a1, 0(t0)\n" ++
  "  jal ra, check_gas_limit\n" ++
  "  bnez a0, .Lvhp_pred_false\n" ++
  "  li t0, 1\n" ++
  "  sd t0, 0(s4)\n" ++
  "  li a0, 0\n" ++
  "  j .Lvhp_ret\n" ++
  ".Lvhp_pred_false:\n" ++
  "  sd zero, 0(s4)\n" ++
  "  li a0, 0\n" ++
  "  j .Lvhp_ret\n" ++
  ".Lvhp_child_parse_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lvhp_ret\n" ++
  ".Lvhp_size_fail:\n" ++
  "  li a0, 2\n" ++
  "  j .Lvhp_ret\n" ++
  ".Lvhp_parent_field_fail:\n" ++
  "  li a0, 3\n" ++
  "  j .Lvhp_ret\n" ++
  ".Lvhp_child_field_fail:\n" ++
  "  li a0, 4\n" ++
  ".Lvhp_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- `zisk_validate_header_pair`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : parent_rlp_len
      bytes  8..16 : child_rlp_len
      bytes 16..   : parent_rlp || child_rlp
    Output layout:
      bytes  0.. 8 : status code (0..4)
      bytes  8..16 : is_valid (1 if all four invariants hold) -/
def ziskValidateHeaderPairPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a1, 8(a7)                # parent_rlp_len\n" ++
  "  ld a3, 16(a7)               # child_rlp_len\n" ++
  "  addi a0, a7, 24             # parent_rlp ptr\n" ++
  "  add a2, a0, a1              # child_rlp ptr\n" ++
  "  li a4, 0xa0010008           # is_valid out\n" ++
  "  jal ra, validate_header_pair\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lvhp_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  zkvmKeccak256Function ++ "\n" ++
  blockHashFromHeaderFunction ++ "\n" ++
  validateParentHashLinkFunction ++ "\n" ++
  checkGasLimitFunction ++ "\n" ++
  validateHeaderPairFunction ++ "\n" ++
  ".Lvhp_pdone:"

def ziskValidateHeaderPairDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  "vphl_offset:\n" ++
  "  .zero 8\n" ++
  "vphl_length:\n" ++
  "  .zero 8\n" ++
  "vphl_claimed:\n" ++
  "  .zero 32\n" ++
  "vphl_computed:\n" ++
  "  .zero 32\n" ++
  "vhp_link_valid:\n" ++
  "  .zero 8\n" ++
  "vhp_parent_number:\n" ++
  "  .zero 8\n" ++
  "vhp_parent_timestamp:\n" ++
  "  .zero 8\n" ++
  "vhp_parent_gas_limit:\n" ++
  "  .zero 8\n" ++
  "vhp_child_number:\n" ++
  "  .zero 8\n" ++
  "vhp_child_timestamp:\n" ++
  "  .zero 8\n" ++
  "vhp_child_gas_limit:\n" ++
  "  .zero 8"

def ziskValidateHeaderPairProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskValidateHeaderPairPrologue
  dataAsm     := ziskValidateHeaderPairDataSection
}

/-! ## validate_header_chain -- PR-K175

    Iterate `validate_header_pair` (K174) over N consecutive
    headers (parent, child) and verify every link in the
    chain. This is the EELS `validate_headers` function: walk
    the witness list and assert each successive pair of
    headers satisfies the four pair invariants:

      1. child.parent_hash == keccak256(parent)
      2. child.number == parent.number + 1
      3. child.timestamp > parent.timestamp
      4. check_gas_limit(child, parent) == 0

    Stops on the first failing pair and reports the failing
    index. Empty (N == 0) and singleton (N == 1) chains are
    accepted vacuously -- there is no pair to check.

    Header layout (one length-prefix table + flat byte blob):
      headers[0] starts at headers_ptr + offsets[0]
      headers[i] has length lengths[i]
      offsets[i+1] = offsets[i] + lengths[i]
    The caller supplies `lengths` (a `u64[N]`); offsets are
    computed inline.

    Calling convention:
      a0 (input)  : header count N
      a1 (input)  : lengths ptr (u64[N], byte lengths)
      a2 (input)  : headers ptr (flat concatenated RLPs)
      a3 (input)  : u64 out (is_valid: 1 if every link OK)
      a4 (input)  : u64 out (first_bad_index: index of the
                    failing pair; 0 if all pairs pass)
      ra (input)  : return
      a0 (output) :
        0 : success -- predicate written
        nonzero : propagated status from validate_header_pair
                  for the first failing pair (1..4) -/
def validateHeaderChainFunction : String :=
  "validate_header_chain:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a0                   # N\n" ++
  "  mv s1, a1                   # lengths ptr\n" ++
  "  mv s2, a2                   # headers ptr\n" ++
  "  mv s3, a3                   # is_valid out\n" ++
  "  mv s4, a4                   # first_bad_index out\n" ++
  "  sd zero, 0(s3)\n" ++
  "  sd zero, 0(s4)\n" ++
  "  # Vacuous-true for N == 0 or N == 1.\n" ++
  "  li t0, 2\n" ++
  "  bltu s0, t0, .Lvhc_vacuous\n" ++
  "  # parent ptr/len start (i = 0)\n" ++
  "  mv s5, s2                   # current parent ptr\n" ++
  "  li s6, 0                    # current index i\n" ++
  ".Lvhc_loop:\n" ++
  "  # Pre-compute child index = i + 1\n" ++
  "  addi t0, s6, 1\n" ++
  "  beq t0, s0, .Lvhc_done       # i+1 == N -> finished\n" ++
  "  # parent_len = lengths[i], child_len = lengths[i+1]\n" ++
  "  slli t1, s6, 3\n" ++
  "  add t1, s1, t1                              # &lengths[i]\n" ++
  "  ld t2, 0(t1)                                # parent_len\n" ++
  "  ld t3, 8(t1)                                # child_len\n" ++
  "  add t4, s5, t2                              # child_ptr = parent_ptr + parent_len\n" ++
  "  mv a0, s5; mv a1, t2\n" ++
  "  mv a2, t4; mv a3, t3\n" ++
  "  la a4, vhc_pair_valid\n" ++
  "  jal ra, validate_header_pair\n" ++
  "  bnez a0, .Lvhc_pair_status_fail\n" ++
  "  la t0, vhc_pair_valid; ld t1, 0(t0)\n" ++
  "  beqz t1, .Lvhc_pred_false\n" ++
  "  # Advance: parent <- child\n" ++
  "  slli t1, s6, 3\n" ++
  "  add t1, s1, t1\n" ++
  "  ld t2, 0(t1)                                # parent_len (just used)\n" ++
  "  add s5, s5, t2                              # parent_ptr += parent_len\n" ++
  "  addi s6, s6, 1\n" ++
  "  j .Lvhc_loop\n" ++
  ".Lvhc_done:\n" ++
  ".Lvhc_vacuous:\n" ++
  "  li t0, 1\n" ++
  "  sd t0, 0(s3)\n" ++
  "  li a0, 0\n" ++
  "  j .Lvhc_ret\n" ++
  ".Lvhc_pred_false:\n" ++
  "  sd zero, 0(s3)\n" ++
  "  sd s6, 0(s4)\n" ++
  "  li a0, 0\n" ++
  "  j .Lvhc_ret\n" ++
  ".Lvhc_pair_status_fail:\n" ++
  "  sd s6, 0(s4)\n" ++
  ".Lvhc_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-- `zisk_validate_header_chain`: probe BuildUnit.
    Input layout:
      bytes  0..  8 : N (header count)
      bytes  8..  8 + 8*N : lengths (u64[N])
      bytes  8 + 8*N .. : concatenated header RLPs
    Output layout:
      bytes  0.. 8 : status code
      bytes  8..16 : is_valid (1 if every link OK)
      bytes 16..24 : first_bad_index -/
def ziskValidateHeaderChainPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a0, 8(a7)                # N\n" ++
  "  addi a1, a7, 16             # lengths ptr\n" ++
  "  slli t0, a0, 3              # 8*N\n" ++
  "  add a2, a1, t0              # headers ptr\n" ++
  "  li a3, 0xa0010008           # is_valid out\n" ++
  "  li a4, 0xa0010010           # first_bad_index out\n" ++
  "  jal ra, validate_header_chain\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lvhc_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  zkvmKeccak256Function ++ "\n" ++
  blockHashFromHeaderFunction ++ "\n" ++
  validateParentHashLinkFunction ++ "\n" ++
  checkGasLimitFunction ++ "\n" ++
  validateHeaderPairFunction ++ "\n" ++
  validateHeaderChainFunction ++ "\n" ++
  ".Lvhc_pdone:"

def ziskValidateHeaderChainDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  "vphl_offset:\n" ++
  "  .zero 8\n" ++
  "vphl_length:\n" ++
  "  .zero 8\n" ++
  "vphl_claimed:\n" ++
  "  .zero 32\n" ++
  "vphl_computed:\n" ++
  "  .zero 32\n" ++
  "vhp_link_valid:\n" ++
  "  .zero 8\n" ++
  "vhp_parent_number:\n" ++
  "  .zero 8\n" ++
  "vhp_parent_timestamp:\n" ++
  "  .zero 8\n" ++
  "vhp_parent_gas_limit:\n" ++
  "  .zero 8\n" ++
  "vhp_child_number:\n" ++
  "  .zero 8\n" ++
  "vhp_child_timestamp:\n" ++
  "  .zero 8\n" ++
  "vhp_child_gas_limit:\n" ++
  "  .zero 8\n" ++
  "vhc_pair_valid:\n" ++
  "  .zero 8"

def ziskValidateHeaderChainProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskValidateHeaderChainPrologue
  dataAsm     := ziskValidateHeaderChainDataSection
}

/-! ## block_hash_array_from_chain -- PR-K187

    Validate an N-element header chain (K175) and, for each
    header, output its block_hash (K172) into a 32*N-byte
    output buffer. Combined output the caller can use to feed
    downstream chain-state machinery (block_hash precompile
    inputs, witness mapping, etc.).

    Iterates over the chain twice in spirit but only once in
    practice: walks `parent <- child` pairs, and for each
    header writes `keccak256(header_rlp)` to the corresponding
    32-byte slot.

    Calling convention:
      a0 (input)  : N (header count)
      a1 (input)  : header_lengths ptr (u64[N])
      a2 (input)  : headers ptr (concatenated)
      a3 (input)  : block_hash_out ptr (32*N bytes)
      a4 (input)  : u64 out (is_valid: 1 if chain accepts)
      a5 (input)  : u64 out (first_bad_index)
      ra (input)  : return
      a0 (output) :
        0 : success -- predicate + block_hashes written
        nonzero : propagated status from validate_header_pair
                  for the first failing link (block_hashes for
                  headers up to and including the failure point
                  are still written)

    Special: for N == 0, write nothing and report is_valid=1.
    For N == 1, validate trivially and write only block_hash[0]. -/
def blockHashArrayFromChainFunction : String :=
  "block_hash_array_from_chain:\n" ++
  "  addi sp, sp, -80\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  sd s8, 72(sp)\n" ++
  "  mv s0, a0                   # N\n" ++
  "  mv s1, a1                   # header_lengths ptr\n" ++
  "  mv s2, a2                   # headers ptr\n" ++
  "  mv s3, a3                   # block_hash_out ptr\n" ++
  "  mv s4, a4                   # is_valid out\n" ++
  "  mv s5, a5                   # first_bad_index out\n" ++
  "  li t0, 1\n" ++
  "  sd t0, 0(s4)                # default is_valid = 1\n" ++
  "  sd zero, 0(s5)\n" ++
  "  beqz s0, .Lbhac_done\n" ++
  "  # Write block_hash[0]\n" ++
  "  ld a1, 0(s1)\n" ++
  "  mv a0, s2; mv a2, s3\n" ++
  "  jal ra, block_hash_from_header\n" ++
  "  li t0, 1\n" ++
  "  beq s0, t0, .Lbhac_done     # N == 1 -> trivially valid\n" ++
  "  # Walk the chain, validating each link and writing block_hashes.\n" ++
  "  mv s6, s2                   # parent ptr = headers[0]\n" ++
  "  li s7, 0                    # i = 0\n" ++
  "  addi s8, s3, 32             # next block_hash slot = block_hash_out + 32\n" ++
  ".Lbhac_loop:\n" ++
  "  addi t0, s7, 1\n" ++
  "  beq t0, s0, .Lbhac_done\n" ++
  "  # parent_len = header_lengths[i]; child_len = header_lengths[i+1]\n" ++
  "  slli t1, s7, 3\n" ++
  "  add t1, s1, t1\n" ++
  "  ld a1, 0(t1)                # parent_len\n" ++
  "  ld a3, 8(t1)                # child_len\n" ++
  "  add t2, s6, a1              # child ptr\n" ++
  "  mv a0, s6\n" ++
  "  mv a2, t2\n" ++
  "  la a4, bhac_pair_valid\n" ++
  "  jal ra, validate_header_pair\n" ++
  "  bnez a0, .Lbhac_status_fail\n" ++
  "  la t0, bhac_pair_valid; ld t1, 0(t0)\n" ++
  "  beqz t1, .Lbhac_pred_false\n" ++
  "  # Write block_hash[i+1]\n" ++
  "  slli t1, s7, 3\n" ++
  "  add t1, s1, t1\n" ++
  "  ld t2, 0(t1)                # parent_len[i]\n" ++
  "  ld t3, 8(t1)                # child_len[i+1] (= header[i+1] len)\n" ++
  "  add t4, s6, t2              # child ptr\n" ++
  "  mv a0, t4; mv a1, t3; mv a2, s8\n" ++
  "  jal ra, block_hash_from_header\n" ++
  "  # Advance\n" ++
  "  slli t1, s7, 3\n" ++
  "  add t1, s1, t1\n" ++
  "  ld t2, 0(t1)\n" ++
  "  add s6, s6, t2              # parent ptr += parent_len\n" ++
  "  addi s8, s8, 32             # next block_hash slot\n" ++
  "  addi s7, s7, 1\n" ++
  "  j .Lbhac_loop\n" ++
  ".Lbhac_pred_false:\n" ++
  "  sd zero, 0(s4)\n" ++
  "  sd s7, 0(s5)\n" ++
  "  li a0, 0\n" ++
  "  j .Lbhac_ret\n" ++
  ".Lbhac_status_fail:\n" ++
  "  sd zero, 0(s4)\n" ++
  "  sd s7, 0(s5)\n" ++
  "  j .Lbhac_ret\n" ++
  ".Lbhac_done:\n" ++
  "  li a0, 0\n" ++
  ".Lbhac_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp)\n" ++
  "  addi sp, sp, 80\n" ++
  "  ret"

/-- `zisk_block_hash_array_from_chain`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : N
      bytes  8..8+8N : header_lengths (u64[N])
      bytes  8+8N.. : concatenated header RLPs
    Output layout:
      bytes  0.. 8 : status
      bytes  8..16 : is_valid
      bytes 16..24 : first_bad_index
      bytes 24..   : block_hash[0], block_hash[1], ... (32*N B)
    Caveat: ziskemu output is capped at 256 B, so this probe
    test is meaningful only for N <= 7 (status+valid+bad = 24,
    remaining 232 B fits 7 hashes). -/
def ziskBlockHashArrayFromChainPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a0, 8(a7)                # N\n" ++
  "  addi a1, a7, 16             # header_lengths ptr\n" ++
  "  slli t0, a0, 3              # 8*N\n" ++
  "  add a2, a1, t0              # headers ptr\n" ++
  "  li a3, 0xa0010018           # block_hash_out at OUTPUT + 24\n" ++
  "  li a4, 0xa0010008           # is_valid\n" ++
  "  li a5, 0xa0010010           # first_bad_index\n" ++
  "  jal ra, block_hash_array_from_chain\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lbhac_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  zkvmKeccak256Function ++ "\n" ++
  blockHashFromHeaderFunction ++ "\n" ++
  validateParentHashLinkFunction ++ "\n" ++
  checkGasLimitFunction ++ "\n" ++
  validateHeaderPairFunction ++ "\n" ++
  blockHashArrayFromChainFunction ++ "\n" ++
  ".Lbhac_pdone:"

def ziskBlockHashArrayFromChainDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  "vphl_offset:\n" ++
  "  .zero 8\n" ++
  "vphl_length:\n" ++
  "  .zero 8\n" ++
  "vphl_claimed:\n" ++
  "  .zero 32\n" ++
  "vphl_computed:\n" ++
  "  .zero 32\n" ++
  "vhp_link_valid:\n" ++
  "  .zero 8\n" ++
  "vhp_parent_number:\n" ++
  "  .zero 8\n" ++
  "vhp_parent_timestamp:\n" ++
  "  .zero 8\n" ++
  "vhp_parent_gas_limit:\n" ++
  "  .zero 8\n" ++
  "vhp_child_number:\n" ++
  "  .zero 8\n" ++
  "vhp_child_timestamp:\n" ++
  "  .zero 8\n" ++
  "vhp_child_gas_limit:\n" ++
  "  .zero 8\n" ++
  "bhac_pair_valid:\n" ++
  "  .zero 8"

def ziskBlockHashArrayFromChainProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBlockHashArrayFromChainPrologue
  dataAsm     := ziskBlockHashArrayFromChainDataSection
}

/-! ## validate_block_hash_chain_match -- PR-K195

    Validate an N-element header chain (K175 invariants) AND
    check that the block_hash of each header (K172) matches a
    caller-supplied claim array. This is the natural primitive
    for chain-anchor proofs: \"the prover claims these are
    block_hashes B[0..N) for blocks H[0..N); verify both that
    the chain is well-formed and that the claimed hashes are
    correct\".

    The two checks (chain validity + hash match) are returned
    via a single is_valid u64; a status code distinguishes
    structural-fail (chain links broken) from hash-mismatch.

    Calling convention:
      a0 (input)  : N (header count)
      a1 (input)  : header_lengths ptr (u64[N])
      a2 (input)  : headers ptr (concatenated)
      a3 (input)  : claimed_hashes ptr (32*N bytes)
      a4 (input)  : u64 out (is_valid)
      a5 (input)  : u64 out (first_bad_index)
      ra (input)  : return
      a0 (output) :
        0 : success -- predicate written
        nonzero : propagated status from validate_header_pair
                  for the first failing link -/
def validateBlockHashChainMatchFunction : String :=
  "validate_block_hash_chain_match:\n" ++
  "  addi sp, sp, -96\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  sd s8, 72(sp); sd s9, 80(sp); sd s10, 88(sp)\n" ++
  "  mv s0, a0                   # N\n" ++
  "  mv s1, a1                   # header_lengths ptr\n" ++
  "  mv s2, a2                   # headers ptr\n" ++
  "  mv s3, a3                   # claimed_hashes ptr (32*N)\n" ++
  "  mv s4, a4                   # is_valid out\n" ++
  "  mv s5, a5                   # first_bad_index out\n" ++
  "  li t0, 1\n" ++
  "  sd t0, 0(s4)\n" ++
  "  sd zero, 0(s5)\n" ++
  "  beqz s0, .Lvbhcm_done       # N==0: vacuous true\n" ++
  "  # ---- Verify block_hash[0] matches ----\n" ++
  "  ld a1, 0(s1)                # header_lengths[0]\n" ++
  "  mv a0, s2                   # header_rlp[0]\n" ++
  "  la a2, vbhcm_hash_buf\n" ++
  "  jal ra, block_hash_from_header\n" ++
  "  la t0, vbhcm_hash_buf; mv t1, s3\n" ++
  "  ld t2,  0(t0); ld t3,  0(t1); bne t2, t3, .Lvbhcm_pred_false\n" ++
  "  ld t2,  8(t0); ld t3,  8(t1); bne t2, t3, .Lvbhcm_pred_false\n" ++
  "  ld t2, 16(t0); ld t3, 16(t1); bne t2, t3, .Lvbhcm_pred_false\n" ++
  "  ld t2, 24(t0); ld t3, 24(t1); bne t2, t3, .Lvbhcm_pred_false\n" ++
  "  li t0, 1\n" ++
  "  beq s0, t0, .Lvbhcm_done    # N==1: just hash check, no chain\n" ++
  "  # ---- Walk chain ----\n" ++
  "  mv s6, s2                   # parent_ptr = headers[0]\n" ++
  "  li s7, 0                    # i = 0\n" ++
  "  addi s8, s3, 32             # next claimed_hash slot\n" ++
  ".Lvbhcm_loop:\n" ++
  "  addi t0, s7, 1\n" ++
  "  beq t0, s0, .Lvbhcm_done\n" ++
  "  slli t1, s7, 3\n" ++
  "  add t1, s1, t1\n" ++
  "  ld a1, 0(t1)                # parent_len\n" ++
  "  ld a3, 8(t1)                # child_len\n" ++
  "  add t2, s6, a1              # child_ptr\n" ++
  "  mv a0, s6\n" ++
  "  mv a2, t2\n" ++
  "  la a4, vbhcm_pair_valid\n" ++
  "  jal ra, validate_header_pair\n" ++
  "  bnez a0, .Lvbhcm_status_fail\n" ++
  "  la t0, vbhcm_pair_valid; ld t1, 0(t0)\n" ++
  "  beqz t1, .Lvbhcm_pred_false\n" ++
  "  # Hash child and compare to claimed\n" ++
  "  slli t1, s7, 3\n" ++
  "  add t1, s1, t1\n" ++
  "  ld t2, 0(t1)                # parent_len\n" ++
  "  ld t3, 8(t1)                # child_len\n" ++
  "  add t4, s6, t2              # child_ptr\n" ++
  "  mv a0, t4; mv a1, t3\n" ++
  "  la a2, vbhcm_hash_buf\n" ++
  "  jal ra, block_hash_from_header\n" ++
  "  la t0, vbhcm_hash_buf; mv t1, s8\n" ++
  "  ld t2,  0(t0); ld t3,  0(t1); bne t2, t3, .Lvbhcm_pred_false\n" ++
  "  ld t2,  8(t0); ld t3,  8(t1); bne t2, t3, .Lvbhcm_pred_false\n" ++
  "  ld t2, 16(t0); ld t3, 16(t1); bne t2, t3, .Lvbhcm_pred_false\n" ++
  "  ld t2, 24(t0); ld t3, 24(t1); bne t2, t3, .Lvbhcm_pred_false\n" ++
  "  # Advance\n" ++
  "  slli t1, s7, 3\n" ++
  "  add t1, s1, t1\n" ++
  "  ld t2, 0(t1)\n" ++
  "  add s6, s6, t2\n" ++
  "  addi s8, s8, 32\n" ++
  "  addi s7, s7, 1\n" ++
  "  j .Lvbhcm_loop\n" ++
  ".Lvbhcm_pred_false:\n" ++
  "  sd zero, 0(s4)\n" ++
  "  sd s7, 0(s5)\n" ++
  "  li a0, 0\n" ++
  "  j .Lvbhcm_ret\n" ++
  ".Lvbhcm_status_fail:\n" ++
  "  sd zero, 0(s4)\n" ++
  "  sd s7, 0(s5)\n" ++
  "  j .Lvbhcm_ret\n" ++
  ".Lvbhcm_done:\n" ++
  "  li a0, 0\n" ++
  ".Lvbhcm_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp); ld s9, 80(sp); ld s10, 88(sp)\n" ++
  "  addi sp, sp, 96\n" ++
  "  ret"

/-- `zisk_validate_block_hash_chain_match`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : N
      bytes  8..8+8N        : header_lengths
      bytes  8+8N..8+8N+32N : claimed_hashes (32 B each)
      bytes  8+40N..        : concatenated header RLPs
    Output layout:
      bytes  0.. 8 : status
      bytes  8..16 : is_valid
      bytes 16..24 : first_bad_index -/
def ziskValidateBlockHashChainMatchPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a0, 8(a7)                # N\n" ++
  "  addi a1, a7, 16             # header_lengths ptr\n" ++
  "  slli t0, a0, 3              # 8*N\n" ++
  "  add a3, a1, t0              # claimed_hashes ptr\n" ++
  "  slli t1, a0, 5              # 32*N\n" ++
  "  add a2, a3, t1              # headers ptr\n" ++
  "  li a4, 0xa0010008           # is_valid out\n" ++
  "  li a5, 0xa0010010           # first_bad_index out\n" ++
  "  jal ra, validate_block_hash_chain_match\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lvbhcm_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  zkvmKeccak256Function ++ "\n" ++
  blockHashFromHeaderFunction ++ "\n" ++
  validateParentHashLinkFunction ++ "\n" ++
  checkGasLimitFunction ++ "\n" ++
  validateHeaderPairFunction ++ "\n" ++
  validateBlockHashChainMatchFunction ++ "\n" ++
  ".Lvbhcm_pdone:"

def ziskValidateBlockHashChainMatchDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  "vphl_offset:\n" ++
  "  .zero 8\n" ++
  "vphl_length:\n" ++
  "  .zero 8\n" ++
  "vphl_claimed:\n" ++
  "  .zero 32\n" ++
  "vphl_computed:\n" ++
  "  .zero 32\n" ++
  "vhp_link_valid:\n" ++
  "  .zero 8\n" ++
  "vhp_parent_number:\n" ++
  "  .zero 8\n" ++
  "vhp_parent_timestamp:\n" ++
  "  .zero 8\n" ++
  "vhp_parent_gas_limit:\n" ++
  "  .zero 8\n" ++
  "vhp_child_number:\n" ++
  "  .zero 8\n" ++
  "vhp_child_timestamp:\n" ++
  "  .zero 8\n" ++
  "vhp_child_gas_limit:\n" ++
  "  .zero 8\n" ++
  "vbhcm_pair_valid:\n" ++
  "  .zero 8\n" ++
  "vbhcm_hash_buf:\n" ++
  "  .zero 32"

def ziskValidateBlockHashChainMatchProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskValidateBlockHashChainMatchPrologue
  dataAsm     := ziskValidateBlockHashChainMatchDataSection
}

/-! ## chain_compute_total_gas_used -- PR-K196

    Aggregate `gas_used` (header field 10) across an N-element
    header chain into a single u64 sum. Useful for chain-state
    commitments and protocol-level invariants such as
    \"this chain segment burned at most G gas total\".

    No chain validation is performed here -- the caller is
    responsible for combining this with K175 (or K195) for
    chain integrity. K196 is purely an aggregator over the
    headers; the inputs and accumulator math are kept in plain
    u64, so the sum saturates / wraps modulo 2^64 like any
    RISC-V add.

    For real mainnet blocks, gas_used <= ~30M and N <= ~256 in
    a single witness; the sum stays well below 2^64.

    Calling convention:
      a0 (input)  : N (header count)
      a1 (input)  : header_lengths ptr (u64[N])
      a2 (input)  : headers ptr (concatenated)
      a3 (input)  : u64 out (total_gas_used; running sum)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse error on some header (sum is partial,
            up to the failing header)
        2 : a header's gas_used field exceeds 8 bytes BE -/
def chainComputeTotalGasUsedFunction : String :=
  "chain_compute_total_gas_used:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0                   # N\n" ++
  "  mv s1, a1                   # header_lengths ptr\n" ++
  "  mv s2, a2                   # headers ptr\n" ++
  "  mv s3, a3                   # out ptr\n" ++
  "  sd zero, 0(s3)\n" ++
  "  li s4, 0                    # i = 0\n" ++
  "  beqz s0, .Lccgu_done\n" ++
  ".Lccgu_loop:\n" ++
  "  beq s4, s0, .Lccgu_done\n" ++
  "  slli t0, s4, 3\n" ++
  "  add t0, s1, t0\n" ++
  "  ld a1, 0(t0)                # header_len\n" ++
  "  mv a0, s2                   # header_ptr\n" ++
  "  li a2, 10                   # field 10 = gas_used\n" ++
  "  la a3, ccgu_field\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  li t0, 1\n" ++
  "  beq a0, t0, .Lccgu_parse_fail\n" ++
  "  li t0, 2\n" ++
  "  beq a0, t0, .Lccgu_size_fail\n" ++
  "  # Accumulate\n" ++
  "  la t0, ccgu_field; ld t1, 0(t0)\n" ++
  "  ld t2, 0(s3)\n" ++
  "  add t2, t2, t1\n" ++
  "  sd t2, 0(s3)\n" ++
  "  # Advance to next header\n" ++
  "  slli t0, s4, 3\n" ++
  "  add t0, s1, t0\n" ++
  "  ld t1, 0(t0)\n" ++
  "  add s2, s2, t1\n" ++
  "  addi s4, s4, 1\n" ++
  "  j .Lccgu_loop\n" ++
  ".Lccgu_done:\n" ++
  "  li a0, 0\n" ++
  "  j .Lccgu_ret\n" ++
  ".Lccgu_parse_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lccgu_ret\n" ++
  ".Lccgu_size_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lccgu_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- `zisk_chain_compute_total_gas_used`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : N
      bytes  8..8+8N : header_lengths
      bytes  8+8N.. : concatenated header RLPs
    Output layout:
      bytes  0.. 8 : status
      bytes  8..16 : total_gas_used -/
def ziskChainComputeTotalGasUsedPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a0, 8(a7)                # N\n" ++
  "  addi a1, a7, 16             # header_lengths ptr\n" ++
  "  slli t0, a0, 3              # 8*N\n" ++
  "  add a2, a1, t0              # headers ptr\n" ++
  "  li a3, 0xa0010008           # total_gas_used out\n" ++
  "  jal ra, chain_compute_total_gas_used\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lccgu_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  chainComputeTotalGasUsedFunction ++ "\n" ++
  ".Lccgu_pdone:"

def ziskChainComputeTotalGasUsedDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  "ccgu_field:\n" ++
  "  .zero 8"

def ziskChainComputeTotalGasUsedProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskChainComputeTotalGasUsedPrologue
  dataAsm     := ziskChainComputeTotalGasUsedDataSection
}

/-! ## chain_extract_number_range -- PR-K197

    Extract `(min_number, max_number)` from an N-element header
    chain. With K175 validated parent-hash invariants, the chain
    has strictly increasing numbers, so this is simply
    `(headers[0].number, headers[N-1].number)`. We return both
    edges so callers can verify `max - min + 1 == N` (the chain
    is dense) or directly use the range as a chain-segment
    identifier.

    Calling convention:
      a0 (input)  : N (header count, must be >= 1)
      a1 (input)  : header_lengths ptr
      a2 (input)  : headers ptr
      a3 (input)  : u64 out (min_number)
      a4 (input)  : u64 out (max_number)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : empty chain (N == 0)
        2 : RLP parse failure on some header
        3 : a header's number field exceeds 8 bytes BE -/
def chainExtractNumberRangeFunction : String :=
  "chain_extract_number_range:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0                   # N\n" ++
  "  mv s1, a1                   # header_lengths\n" ++
  "  mv s2, a2                   # headers\n" ++
  "  mv s3, a3                   # min out\n" ++
  "  mv s4, a4                   # max out\n" ++
  "  beqz s0, .Lcenr_empty\n" ++
  "  # min = headers[0].number\n" ++
  "  ld a1, 0(s1)\n" ++
  "  mv a0, s2\n" ++
  "  li a2, 8                    # field 8 = number\n" ++
  "  mv a3, s3\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lcenr_propagate\n" ++
  "  # Advance to last header: skip the first (N-1) headers\n" ++
  "  mv t1, s2\n" ++
  "  mv t2, s1\n" ++
  "  addi t3, s0, -1             # iterations = N-1\n" ++
  ".Lcenr_skip:\n" ++
  "  beqz t3, .Lcenr_at_last\n" ++
  "  ld t4, 0(t2)\n" ++
  "  add t1, t1, t4\n" ++
  "  addi t2, t2, 8\n" ++
  "  addi t3, t3, -1\n" ++
  "  j .Lcenr_skip\n" ++
  ".Lcenr_at_last:\n" ++
  "  ld a1, 0(t2)                # length of last header\n" ++
  "  mv a0, t1\n" ++
  "  li a2, 8\n" ++
  "  mv a3, s4\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lcenr_propagate\n" ++
  "  li a0, 0\n" ++
  "  j .Lcenr_ret\n" ++
  ".Lcenr_empty:\n" ++
  "  li a0, 1\n" ++
  "  j .Lcenr_ret\n" ++
  ".Lcenr_propagate:\n" ++
  "  addi a0, a0, 1              # remap rlp_field_to_u64 1/2 -> 2/3\n" ++
  ".Lcenr_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- `zisk_chain_extract_number_range`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : N
      bytes  8..8+8N : header_lengths
      bytes  8+8N.. : concatenated headers
    Output layout:
      bytes  0.. 8 : status
      bytes  8..16 : min_number
      bytes 16..24 : max_number -/
def ziskChainExtractNumberRangePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a0, 8(a7)                # N\n" ++
  "  addi a1, a7, 16             # header_lengths\n" ++
  "  slli t0, a0, 3\n" ++
  "  add a2, a1, t0              # headers\n" ++
  "  li a3, 0xa0010008           # min out\n" ++
  "  li a4, 0xa0010010           # max out\n" ++
  "  jal ra, chain_extract_number_range\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lcenr_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  chainExtractNumberRangeFunction ++ "\n" ++
  ".Lcenr_pdone:"

def ziskChainExtractNumberRangeDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8"

def ziskChainExtractNumberRangeProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskChainExtractNumberRangePrologue
  dataAsm     := ziskChainExtractNumberRangeDataSection
}

/-! ## header_extract_basefee -- PR-K198

    Extract `base_fee_per_gas` (field 15, present from London
    onwards) from a header RLP. Returns the value as a u64; the
    EIP-1559 base_fee is bounded by `2^256-1` in principle but
    in practice never exceeds u64 in any chain we care about.
    Callers that need the full uint256 form should use the more
    general `rlp_field_to_u256` (not yet implemented) instead.

    Field index 15 is the **first** post-London field; on
    pre-London headers (`len(fields) <= 15`) the call yields
    a parse-failure status.

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp byte length
      a2 (input)  : u64 out (base_fee_per_gas)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse failure / field 15 missing (pre-London)
        2 : base_fee field exceeds 8 bytes BE -/
def headerExtractBasefeeFunction : String :=
  "header_extract_basefee:\n" ++
  "  addi sp, sp, -16\n" ++
  "  sd ra, 0(sp)\n" ++
  "  # rlp_field_to_u64(a0=header_ptr, a1=len, a2=15, a3=output_ptr)\n" ++
  "  mv a3, a2                   # output ptr (caller-supplied) -> a3\n" ++
  "  li a2, 15                   # field index = 15 (base_fee)\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  ld ra, 0(sp)\n" ++
  "  addi sp, sp, 16\n" ++
  "  ret"

/-- `zisk_header_extract_basefee`: probe BuildUnit.
    Input layout:
      bytes 0..8  : header_rlp_len
      bytes 8..   : header_rlp
    Output layout:
      bytes 0..8  : status
      bytes 8..16 : base_fee_per_gas -/
def ziskHeaderExtractBasefeePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a1, 8(a7)                # header_rlp_len\n" ++
  "  addi a0, a7, 16             # header_rlp ptr\n" ++
  "  li a2, 0xa0010008           # base_fee out\n" ++
  "  jal ra, header_extract_basefee\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lheb_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  headerExtractBasefeeFunction ++ "\n" ++
  ".Lheb_pdone:"

def ziskHeaderExtractBasefeeDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8"

def ziskHeaderExtractBasefeeProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskHeaderExtractBasefeePrologue
  dataAsm     := ziskHeaderExtractBasefeeDataSection
}

/-! ## chain_extract_basefee_range -- PR-K199

    Walk an N-element header chain and compute `(min, max)` of
    `base_fee_per_gas` (field 15). London+ only. Useful for
    chain-level base_fee bounds analysis.

    Returns vacuous `(0, 0)` on N == 0.

    Calling convention:
      a0 (input)  : N (header count)
      a1 (input)  : header_lengths ptr
      a2 (input)  : headers ptr
      a3 (input)  : u64 out (min)
      a4 (input)  : u64 out (max)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : a header parse failure (e.g., pre-London header)
        2 : a base_fee field exceeds 8 bytes BE -/
def chainExtractBasefeeRangeFunction : String :=
  "chain_extract_basefee_range:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0                   # N\n" ++
  "  mv s1, a1                   # header_lengths\n" ++
  "  mv s2, a2                   # headers\n" ++
  "  mv s3, a3                   # min out\n" ++
  "  mv s4, a4                   # max out\n" ++
  "  sd zero, 0(s3)\n" ++
  "  sd zero, 0(s4)\n" ++
  "  beqz s0, .Lcebr_done\n" ++
  "  # Initialize min/max with headers[0].basefee\n" ++
  "  ld a1, 0(s1)\n" ++
  "  mv a0, s2\n" ++
  "  mv a2, s3\n" ++
  "  jal ra, header_extract_basefee\n" ++
  "  bnez a0, .Lcebr_ret\n" ++
  "  ld t0, 0(s3)\n" ++
  "  sd t0, 0(s4)                # max = min = first value\n" ++
  "  # Walk remaining headers\n" ++
  "  ld t1, 0(s1)\n" ++
  "  add t2, s2, t1              # next header ptr\n" ++
  "  addi t3, s1, 8              # next length ptr\n" ++
  "  li t4, 1                    # i\n" ++
  ".Lcebr_loop:\n" ++
  "  beq t4, s0, .Lcebr_done\n" ++
  "  ld a1, 0(t3)\n" ++
  "  mv a0, t2\n" ++
  "  la a2, cebr_cur\n" ++
  "  # Stash t2/t3/t4 in s-regs since rlp_field_to_u64 will\n" ++
  "  # save/restore s0..s4 around it; pin them here.\n" ++
  "  # Actually simpler: keep t2/t3/t4 across the call by\n" ++
  "  # using callee-saved regs. We'll re-derive them after.\n" ++
  "  jal ra, header_extract_basefee\n" ++
  "  bnez a0, .Lcebr_ret\n" ++
  "  # cur < min -> update min; cur > max -> update max\n" ++
  "  la t0, cebr_cur; ld t1, 0(t0)\n" ++
  "  ld t5, 0(s3)\n" ++
  "  bgeu t1, t5, .Lcebr_skip_min\n" ++
  "  sd t1, 0(s3)\n" ++
  ".Lcebr_skip_min:\n" ++
  "  ld t5, 0(s4)\n" ++
  "  bleu t1, t5, .Lcebr_skip_max\n" ++
  "  sd t1, 0(s4)\n" ++
  ".Lcebr_skip_max:\n" ++
  "  # Re-derive iteration state. Since we don't have callee-\n" ++
  "  # saved scratch left (s0..s4 all used), maintain t-regs\n" ++
  "  # before the call by stashing on .data.\n" ++
  "  la t0, cebr_i; ld t4, 0(t0)\n" ++
  "  la t0, cebr_hdr_ptr; ld t2, 0(t0)\n" ++
  "  la t0, cebr_len_ptr; ld t3, 0(t0)\n" ++
  "  ld t1, 0(t3)\n" ++
  "  add t2, t2, t1\n" ++
  "  addi t3, t3, 8\n" ++
  "  addi t4, t4, 1\n" ++
  "  la t0, cebr_i;        sd t4, 0(t0)\n" ++
  "  la t0, cebr_hdr_ptr;  sd t2, 0(t0)\n" ++
  "  la t0, cebr_len_ptr;  sd t3, 0(t0)\n" ++
  "  j .Lcebr_loop\n" ++
  ".Lcebr_done:\n" ++
  "  li a0, 0\n" ++
  ".Lcebr_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- `zisk_chain_extract_basefee_range`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : N
      bytes  8..8+8N : header_lengths
      bytes  8+8N.. : concatenated headers
    Output layout:
      bytes  0.. 8 : status
      bytes  8..16 : min_basefee
      bytes 16..24 : max_basefee -/
def ziskChainExtractBasefeeRangePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a0, 8(a7)                # N\n" ++
  "  addi a1, a7, 16\n" ++
  "  slli t0, a0, 3\n" ++
  "  add a2, a1, t0\n" ++
  "  # Pre-init iteration scratch only when N > 0.\n" ++
  "  beqz a0, .Lcebr_skip_init\n" ++
  "  ld t1, 0(a1)                # first header_len\n" ++
  "  add t2, a2, t1              # second header ptr\n" ++
  "  addi t3, a1, 8\n" ++
  "  la t0, cebr_hdr_ptr; sd t2, 0(t0)\n" ++
  "  la t0, cebr_len_ptr; sd t3, 0(t0)\n" ++
  "  la t0, cebr_i; li t4, 1; sd t4, 0(t0)\n" ++
  ".Lcebr_skip_init:\n" ++
  "  li a3, 0xa0010008\n" ++
  "  li a4, 0xa0010010\n" ++
  "  jal ra, chain_extract_basefee_range\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lcebr_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  headerExtractBasefeeFunction ++ "\n" ++
  chainExtractBasefeeRangeFunction ++ "\n" ++
  ".Lcebr_pdone:"

def ziskChainExtractBasefeeRangeDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  "cebr_cur:\n" ++
  "  .zero 8\n" ++
  "cebr_hdr_ptr:\n" ++
  "  .zero 8\n" ++
  "cebr_len_ptr:\n" ++
  "  .zero 8\n" ++
  "cebr_i:\n" ++
  "  .zero 8"

def ziskChainExtractBasefeeRangeProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskChainExtractBasefeeRangePrologue
  dataAsm     := ziskChainExtractBasefeeRangeDataSection
}

/-! ## chain_block_hashes_commitment -- PR-K200

    Compute a 32-byte commitment over the block_hashes of an
    N-element header chain:

      commitment = keccak256( H[0] || H[1] || ... || H[N-1] )

    where `H[i] = keccak256(headers[i])`. This is the natural
    succinct commitment to a chain of block hashes, useful for
    bridges, light clients, and inter-prover commitments.

    For N == 0 the commitment is `keccak256("")` (the empty-
    string hash), which equals
    `0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470`.

    Calling convention:
      a0 (input)  : N (header count)
      a1 (input)  : header_lengths ptr
      a2 (input)  : headers ptr
      a3 (input)  : 32-byte output ptr (commitment)
      ra (input)  : return
      a0 (output) :
        0 : success

    Uses a scratch buffer (`cbhc_concat_buf`) of size 32*MAX_N
    bytes for the intermediate concatenation. MAX_N is fixed
    at 64 in this implementation (sufficient for typical
    stateless witnesses of ~32 headers). -/
def chainBlockHashesCommitmentFunction : String :=
  "chain_block_hashes_commitment:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0                   # N\n" ++
  "  mv s1, a1                   # header_lengths\n" ++
  "  mv s2, a2                   # headers\n" ++
  "  mv s3, a3                   # output ptr\n" ++
  "  la s4, cbhc_concat_buf      # concat buffer start\n" ++
  "  # Walk and hash each header into the concat buffer.\n" ++
  "  li t6, 0                    # i = 0\n" ++
  "  mv t5, s2                   # current header ptr\n" ++
  "  la t4, cbhc_concat_buf\n" ++
  ".Lcbhc_loop:\n" ++
  "  beq t6, s0, .Lcbhc_done\n" ++
  "  # Stash iteration state into .data\n" ++
  "  la t0, cbhc_i; sd t6, 0(t0)\n" ++
  "  la t0, cbhc_hdr_ptr; sd t5, 0(t0)\n" ++
  "  la t0, cbhc_concat_cursor; sd t4, 0(t0)\n" ++
  "  slli t0, t6, 3\n" ++
  "  add t0, s1, t0\n" ++
  "  ld a1, 0(t0)                # header_len\n" ++
  "  mv a0, t5\n" ++
  "  mv a2, t4                   # write into concat buf\n" ++
  "  jal ra, block_hash_from_header\n" ++
  "  # Reload iteration state\n" ++
  "  la t0, cbhc_i; ld t6, 0(t0)\n" ++
  "  la t0, cbhc_hdr_ptr; ld t5, 0(t0)\n" ++
  "  la t0, cbhc_concat_cursor; ld t4, 0(t0)\n" ++
  "  # Advance: concat += 32; header += header_len; i += 1\n" ++
  "  slli t0, t6, 3\n" ++
  "  add t0, s1, t0\n" ++
  "  ld t1, 0(t0)\n" ++
  "  add t5, t5, t1\n" ++
  "  addi t4, t4, 32\n" ++
  "  addi t6, t6, 1\n" ++
  "  j .Lcbhc_loop\n" ++
  ".Lcbhc_done:\n" ++
  "  # commit = keccak256(concat buf, 32*N) -> output\n" ++
  "  la a0, cbhc_concat_buf\n" ++
  "  slli a1, s0, 5              # 32*N\n" ++
  "  mv a2, s3\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  li a0, 0\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- `zisk_chain_block_hashes_commitment`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : N
      bytes  8..8+8N : header_lengths
      bytes  8+8N.. : concatenated headers
    Output layout:
      bytes 0..32 : 32-byte commitment -/
def ziskChainBlockHashesCommitmentPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a0, 8(a7)                # N\n" ++
  "  addi a1, a7, 16\n" ++
  "  slli t0, a0, 3\n" ++
  "  add a2, a1, t0\n" ++
  "  li a3, 0xa0010000           # 32 B commitment out\n" ++
  "  jal ra, chain_block_hashes_commitment\n" ++
  "  j .Lcbhc_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  blockHashFromHeaderFunction ++ "\n" ++
  chainBlockHashesCommitmentFunction ++ "\n" ++
  ".Lcbhc_pdone:"

def ziskChainBlockHashesCommitmentDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "cbhc_concat_buf:\n" ++
  "  .zero 2048                  # 32 * 64 = 2048\n" ++
  "cbhc_i:\n" ++
  "  .zero 8\n" ++
  "cbhc_hdr_ptr:\n" ++
  "  .zero 8\n" ++
  "cbhc_concat_cursor:\n" ++
  "  .zero 8"

def ziskChainBlockHashesCommitmentProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskChainBlockHashesCommitmentPrologue
  dataAsm     := ziskChainBlockHashesCommitmentDataSection
}

/-! ## header_extract_state_root -- PR-K201

    Extract `state_root` (field 3, 32 bytes) from a header RLP
    and copy it to a caller-supplied 32-byte output buffer.

    `header_minimal_decode` already extracts state_root as part
    of a 4-field bundle (parent_hash + state_root + number +
    timestamp); this primitive is the tight standalone variant
    for callers that only need the state_root.

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp byte length
      a2 (input)  : 32-byte output ptr
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse failure / field 3 missing
        2 : field 3 length != 32 -/
def headerExtractStateRootFunction : String :=
  "header_extract_state_root:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0\n" ++
  "  mv s1, a1\n" ++
  "  mv s2, a2\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 3\n" ++
  "  la a3, hesr_offset; la a4, hesr_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lhesr_parse_fail\n" ++
  "  la t0, hesr_length; ld t1, 0(t0)\n" ++
  "  li t2, 32\n" ++
  "  bne t1, t2, .Lhesr_size_fail\n" ++
  "  la t0, hesr_offset; ld t1, 0(t0)\n" ++
  "  add t3, s0, t1\n" ++
  "  ld t4,  0(t3); sd t4,  0(s2)\n" ++
  "  ld t4,  8(t3); sd t4,  8(s2)\n" ++
  "  ld t4, 16(t3); sd t4, 16(s2)\n" ++
  "  ld t4, 24(t3); sd t4, 24(s2)\n" ++
  "  li a0, 0\n" ++
  "  j .Lhesr_ret\n" ++
  ".Lhesr_parse_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lhesr_ret\n" ++
  ".Lhesr_size_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lhesr_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_header_extract_state_root`: probe BuildUnit.
    Input layout:
      bytes 0..8 : header_rlp_len
      bytes 8..  : header_rlp
    Output layout:
      bytes  0.. 8 : status
      bytes  8..40 : 32-byte state_root -/
def ziskHeaderExtractStateRootPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a1, 8(a7)                # header_rlp_len\n" ++
  "  addi a0, a7, 16             # header_rlp ptr\n" ++
  "  li a2, 0xa0010008           # 32 B output\n" ++
  "  jal ra, header_extract_state_root\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lhesr_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  headerExtractStateRootFunction ++ "\n" ++
  ".Lhesr_pdone:"

def ziskHeaderExtractStateRootDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "hesr_offset:\n" ++
  "  .zero 8\n" ++
  "hesr_length:\n" ++
  "  .zero 8"

def ziskHeaderExtractStateRootProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskHeaderExtractStateRootPrologue
  dataAsm     := ziskHeaderExtractStateRootDataSection
}

/-! ## header_extract_parent_hash -- PR-K202

    Extract `parent_hash` (field 0, 32 bytes) from a header
    RLP and copy it to a caller-supplied 32-byte output buffer.
    Standalone variant of the field-0 access already inside
    K17 / K94 / K173 / K183.

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp byte length
      a2 (input)  : 32-byte output ptr
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse failure / field 0 missing
        2 : field 0 length != 32 -/
def headerExtractParentHashFunction : String :=
  "header_extract_parent_hash:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0\n" ++
  "  mv s1, a1\n" ++
  "  mv s2, a2\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 0\n" ++
  "  la a3, heph_offset; la a4, heph_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lheph_parse_fail\n" ++
  "  la t0, heph_length; ld t1, 0(t0)\n" ++
  "  li t2, 32\n" ++
  "  bne t1, t2, .Lheph_size_fail\n" ++
  "  la t0, heph_offset; ld t1, 0(t0)\n" ++
  "  add t3, s0, t1\n" ++
  "  ld t4,  0(t3); sd t4,  0(s2)\n" ++
  "  ld t4,  8(t3); sd t4,  8(s2)\n" ++
  "  ld t4, 16(t3); sd t4, 16(s2)\n" ++
  "  ld t4, 24(t3); sd t4, 24(s2)\n" ++
  "  li a0, 0\n" ++
  "  j .Lheph_ret\n" ++
  ".Lheph_parse_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lheph_ret\n" ++
  ".Lheph_size_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lheph_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_header_extract_parent_hash`: probe BuildUnit. -/
def ziskHeaderExtractParentHashPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a1, 8(a7)\n" ++
  "  addi a0, a7, 16\n" ++
  "  li a2, 0xa0010008\n" ++
  "  jal ra, header_extract_parent_hash\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lheph_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  headerExtractParentHashFunction ++ "\n" ++
  ".Lheph_pdone:"

def ziskHeaderExtractParentHashDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "heph_offset:\n" ++
  "  .zero 8\n" ++
  "heph_length:\n" ++
  "  .zero 8"

def ziskHeaderExtractParentHashProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskHeaderExtractParentHashPrologue
  dataAsm     := ziskHeaderExtractParentHashDataSection
}

/-! ## header_extract_receipts_root -- PR-K203

    Extract `receipts_root` (field 5, 32 bytes) from a header
    RLP and copy it to a caller-supplied 32-byte output buffer.

    Tight standalone analogue of K201 (state_root, field 3)
    and K202 (parent_hash, field 0).

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp byte length
      a2 (input)  : 32-byte output ptr
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse failure / field 5 missing
        2 : field 5 length != 32 -/
def headerExtractReceiptsRootFunction : String :=
  "header_extract_receipts_root:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0\n" ++
  "  mv s1, a1\n" ++
  "  mv s2, a2\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 5\n" ++
  "  la a3, herr_offset; la a4, herr_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lherr_parse_fail\n" ++
  "  la t0, herr_length; ld t1, 0(t0)\n" ++
  "  li t2, 32\n" ++
  "  bne t1, t2, .Lherr_size_fail\n" ++
  "  la t0, herr_offset; ld t1, 0(t0)\n" ++
  "  add t3, s0, t1\n" ++
  "  ld t4,  0(t3); sd t4,  0(s2)\n" ++
  "  ld t4,  8(t3); sd t4,  8(s2)\n" ++
  "  ld t4, 16(t3); sd t4, 16(s2)\n" ++
  "  ld t4, 24(t3); sd t4, 24(s2)\n" ++
  "  li a0, 0\n" ++
  "  j .Lherr_ret\n" ++
  ".Lherr_parse_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lherr_ret\n" ++
  ".Lherr_size_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lherr_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_header_extract_receipts_root`: probe BuildUnit. -/
def ziskHeaderExtractReceiptsRootPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a1, 8(a7)\n" ++
  "  addi a0, a7, 16\n" ++
  "  li a2, 0xa0010008\n" ++
  "  jal ra, header_extract_receipts_root\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lherr_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  headerExtractReceiptsRootFunction ++ "\n" ++
  ".Lherr_pdone:"

def ziskHeaderExtractReceiptsRootDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "herr_offset:\n" ++
  "  .zero 8\n" ++
  "herr_length:\n" ++
  "  .zero 8"

def ziskHeaderExtractReceiptsRootProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskHeaderExtractReceiptsRootPrologue
  dataAsm     := ziskHeaderExtractReceiptsRootDataSection
}

/-! ## header_extract_transactions_root -- PR-K204

    Extract `transactions_root` (field 4, 32 bytes) from a
    header RLP. Tight standalone analogue of K201 / K202 / K203.

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp byte length
      a2 (input)  : 32-byte output ptr
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse failure / field 4 missing
        2 : field 4 length != 32 -/
def headerExtractTransactionsRootFunction : String :=
  "header_extract_transactions_root:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0\n" ++
  "  mv s1, a1\n" ++
  "  mv s2, a2\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 4\n" ++
  "  la a3, hetr_offset; la a4, hetr_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lhetr_parse_fail\n" ++
  "  la t0, hetr_length; ld t1, 0(t0)\n" ++
  "  li t2, 32\n" ++
  "  bne t1, t2, .Lhetr_size_fail\n" ++
  "  la t0, hetr_offset; ld t1, 0(t0)\n" ++
  "  add t3, s0, t1\n" ++
  "  ld t4,  0(t3); sd t4,  0(s2)\n" ++
  "  ld t4,  8(t3); sd t4,  8(s2)\n" ++
  "  ld t4, 16(t3); sd t4, 16(s2)\n" ++
  "  ld t4, 24(t3); sd t4, 24(s2)\n" ++
  "  li a0, 0\n" ++
  "  j .Lhetr_ret\n" ++
  ".Lhetr_parse_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lhetr_ret\n" ++
  ".Lhetr_size_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lhetr_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_header_extract_transactions_root`: probe BuildUnit. -/
def ziskHeaderExtractTransactionsRootPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a1, 8(a7)\n" ++
  "  addi a0, a7, 16\n" ++
  "  li a2, 0xa0010008\n" ++
  "  jal ra, header_extract_transactions_root\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lhetr_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  headerExtractTransactionsRootFunction ++ "\n" ++
  ".Lhetr_pdone:"

def ziskHeaderExtractTransactionsRootDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "hetr_offset:\n" ++
  "  .zero 8\n" ++
  "hetr_length:\n" ++
  "  .zero 8"

def ziskHeaderExtractTransactionsRootProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskHeaderExtractTransactionsRootPrologue
  dataAsm     := ziskHeaderExtractTransactionsRootDataSection
}

/-! ## header_extract_withdrawals_root -- PR-K205

    Extract `withdrawals_root` (field 16, 32 bytes) from a
    Shanghai+ header RLP. Tight standalone analogue of K201..
    K204 for the post-Shanghai field 16.

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp byte length
      a2 (input)  : 32-byte output ptr
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse failure / field 16 missing (pre-Shanghai)
        2 : field 16 length != 32 -/
def headerExtractWithdrawalsRootFunction : String :=
  "header_extract_withdrawals_root:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0\n" ++
  "  mv s1, a1\n" ++
  "  mv s2, a2\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 16\n" ++
  "  la a3, hewr_offset; la a4, hewr_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lhewr_parse_fail\n" ++
  "  la t0, hewr_length; ld t1, 0(t0)\n" ++
  "  li t2, 32\n" ++
  "  bne t1, t2, .Lhewr_size_fail\n" ++
  "  la t0, hewr_offset; ld t1, 0(t0)\n" ++
  "  add t3, s0, t1\n" ++
  "  ld t4,  0(t3); sd t4,  0(s2)\n" ++
  "  ld t4,  8(t3); sd t4,  8(s2)\n" ++
  "  ld t4, 16(t3); sd t4, 16(s2)\n" ++
  "  ld t4, 24(t3); sd t4, 24(s2)\n" ++
  "  li a0, 0\n" ++
  "  j .Lhewr_ret\n" ++
  ".Lhewr_parse_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lhewr_ret\n" ++
  ".Lhewr_size_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lhewr_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_header_extract_withdrawals_root`: probe BuildUnit. -/
def ziskHeaderExtractWithdrawalsRootPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a1, 8(a7)\n" ++
  "  addi a0, a7, 16\n" ++
  "  li a2, 0xa0010008\n" ++
  "  jal ra, header_extract_withdrawals_root\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lhewr_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  headerExtractWithdrawalsRootFunction ++ "\n" ++
  ".Lhewr_pdone:"

def ziskHeaderExtractWithdrawalsRootDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "hewr_offset:\n" ++
  "  .zero 8\n" ++
  "hewr_length:\n" ++
  "  .zero 8"

def ziskHeaderExtractWithdrawalsRootProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskHeaderExtractWithdrawalsRootPrologue
  dataAsm     := ziskHeaderExtractWithdrawalsRootDataSection
}

/-! ## header_extract_ommers_hash -- PR-K206

    Extract `ommers_hash` (field 1, 32 bytes) -- post-merge
    always equal to `keccak256(rlp([])) = 0x1dcc4de8...`. Tight
    standalone analogue of K201..K205. -/
def headerExtractOmmersHashFunction : String :=
  "header_extract_ommers_hash:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0\n" ++
  "  mv s1, a1\n" ++
  "  mv s2, a2\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 1\n" ++
  "  la a3, heoh_offset; la a4, heoh_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lheoh_parse_fail\n" ++
  "  la t0, heoh_length; ld t1, 0(t0)\n" ++
  "  li t2, 32\n" ++
  "  bne t1, t2, .Lheoh_size_fail\n" ++
  "  la t0, heoh_offset; ld t1, 0(t0)\n" ++
  "  add t3, s0, t1\n" ++
  "  ld t4,  0(t3); sd t4,  0(s2)\n" ++
  "  ld t4,  8(t3); sd t4,  8(s2)\n" ++
  "  ld t4, 16(t3); sd t4, 16(s2)\n" ++
  "  ld t4, 24(t3); sd t4, 24(s2)\n" ++
  "  li a0, 0\n" ++
  "  j .Lheoh_ret\n" ++
  ".Lheoh_parse_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lheoh_ret\n" ++
  ".Lheoh_size_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lheoh_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

def ziskHeaderExtractOmmersHashPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a1, 8(a7)\n" ++
  "  addi a0, a7, 16\n" ++
  "  li a2, 0xa0010008\n" ++
  "  jal ra, header_extract_ommers_hash\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lheoh_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  headerExtractOmmersHashFunction ++ "\n" ++
  ".Lheoh_pdone:"

def ziskHeaderExtractOmmersHashDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "heoh_offset:\n" ++
  "  .zero 8\n" ++
  "heoh_length:\n" ++
  "  .zero 8"

def ziskHeaderExtractOmmersHashProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskHeaderExtractOmmersHashPrologue
  dataAsm     := ziskHeaderExtractOmmersHashDataSection
}

/-! ## header_extract_prev_randao -- PR-K207

    Extract `prev_randao` (field 13, 32 bytes; was `mix_hash`
    pre-merge). Source of post-merge randomness. Tight
    standalone analogue of the field-1/3/5 extractors. -/
def headerExtractPrevRandaoFunction : String :=
  "header_extract_prev_randao:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0\n" ++
  "  mv s1, a1\n" ++
  "  mv s2, a2\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 13\n" ++
  "  la a3, hepr_offset; la a4, hepr_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lhepr_parse_fail\n" ++
  "  la t0, hepr_length; ld t1, 0(t0)\n" ++
  "  li t2, 32\n" ++
  "  bne t1, t2, .Lhepr_size_fail\n" ++
  "  la t0, hepr_offset; ld t1, 0(t0)\n" ++
  "  add t3, s0, t1\n" ++
  "  ld t4,  0(t3); sd t4,  0(s2)\n" ++
  "  ld t4,  8(t3); sd t4,  8(s2)\n" ++
  "  ld t4, 16(t3); sd t4, 16(s2)\n" ++
  "  ld t4, 24(t3); sd t4, 24(s2)\n" ++
  "  li a0, 0\n" ++
  "  j .Lhepr_ret\n" ++
  ".Lhepr_parse_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lhepr_ret\n" ++
  ".Lhepr_size_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lhepr_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

def ziskHeaderExtractPrevRandaoPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a1, 8(a7)\n" ++
  "  addi a0, a7, 16\n" ++
  "  li a2, 0xa0010008\n" ++
  "  jal ra, header_extract_prev_randao\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lhepr_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  headerExtractPrevRandaoFunction ++ "\n" ++
  ".Lhepr_pdone:"

def ziskHeaderExtractPrevRandaoDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "hepr_offset:\n" ++
  "  .zero 8\n" ++
  "hepr_length:\n" ++
  "  .zero 8"

def ziskHeaderExtractPrevRandaoProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskHeaderExtractPrevRandaoPrologue
  dataAsm     := ziskHeaderExtractPrevRandaoDataSection
}

/-! ## header_extract_beneficiary -- PR-K208

    Extract `beneficiary` / `coinbase` (field 2, 20 bytes) from
    a header RLP. The 20-byte analogue of the K201..K207 family
    of 32-byte single-field extractors.

    Note: K68 `coinbase_extract_from_header` already exists and
    handles the same field; this is the canonical
    `header_extract_*` shape for consistency with the
    K201..K207 naming convention.

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp byte length
      a2 (input)  : 20-byte output ptr
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse failure / field 2 missing
        2 : field 2 length != 20 -/
def headerExtractBeneficiaryFunction : String :=
  "header_extract_beneficiary:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0\n" ++
  "  mv s1, a1\n" ++
  "  mv s2, a2\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 2\n" ++
  "  la a3, hebe_offset; la a4, hebe_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lhebe_parse_fail\n" ++
  "  la t0, hebe_length; ld t1, 0(t0)\n" ++
  "  li t2, 20\n" ++
  "  bne t1, t2, .Lhebe_size_fail\n" ++
  "  la t0, hebe_offset; ld t1, 0(t0)\n" ++
  "  add t3, s0, t1\n" ++
  "  # 20 bytes = 2 × ld + 1 × lwu / sw\n" ++
  "  ld t4,  0(t3); sd t4,  0(s2)\n" ++
  "  ld t4,  8(t3); sd t4,  8(s2)\n" ++
  "  lwu t4, 16(t3); sw t4, 16(s2)\n" ++
  "  li a0, 0\n" ++
  "  j .Lhebe_ret\n" ++
  ".Lhebe_parse_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lhebe_ret\n" ++
  ".Lhebe_size_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lhebe_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_header_extract_beneficiary`: probe BuildUnit. -/
def ziskHeaderExtractBeneficiaryPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a1, 8(a7)\n" ++
  "  addi a0, a7, 16\n" ++
  "  li a2, 0xa0010008\n" ++
  "  jal ra, header_extract_beneficiary\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lhebe_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  headerExtractBeneficiaryFunction ++ "\n" ++
  ".Lhebe_pdone:"

def ziskHeaderExtractBeneficiaryDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "hebe_offset:\n" ++
  "  .zero 8\n" ++
  "hebe_length:\n" ++
  "  .zero 8"

def ziskHeaderExtractBeneficiaryProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskHeaderExtractBeneficiaryPrologue
  dataAsm     := ziskHeaderExtractBeneficiaryDataSection
}

/-! ## block_hash_matches -- PR-K209

    Given a header RLP and a caller-supplied claimed 32-byte
    `block_hash`, verify that
    `keccak256(header_rlp) == claimed_block_hash`. Returns the
    predicate via the `is_valid` output.

    Useful for light-client / bridge proofs where the caller
    has a trusted block_hash from elsewhere and wants to confirm
    the locally-held header RLP matches.

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp byte length
      a2 (input)  : claimed_block_hash ptr (32 bytes)
      a3 (input)  : u64 out (is_valid: 1 if matches, else 0)
      ra (input)  : return
      a0 (output) : 0 (always succeeds; predicate is in is_valid) -/
def blockHashMatchesFunction : String :=
  "block_hash_matches:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a2                   # claimed_hash ptr\n" ++
  "  mv s1, a3                   # is_valid out\n" ++
  "  sd zero, 0(s1)\n" ++
  "  # Compute keccak256(header_rlp) into bhm_computed\n" ++
  "  la a2, bhm_computed\n" ++
  "  jal ra, block_hash_from_header\n" ++
  "  # Compare 32 bytes (4 × 8B)\n" ++
  "  la t0, bhm_computed\n" ++
  "  ld t2,  0(t0); ld t3,  0(s0); bne t2, t3, .Lbhm_neq\n" ++
  "  ld t2,  8(t0); ld t3,  8(s0); bne t2, t3, .Lbhm_neq\n" ++
  "  ld t2, 16(t0); ld t3, 16(s0); bne t2, t3, .Lbhm_neq\n" ++
  "  ld t2, 24(t0); ld t3, 24(s0); bne t2, t3, .Lbhm_neq\n" ++
  "  li t0, 1\n" ++
  "  sd t0, 0(s1)\n" ++
  ".Lbhm_neq:\n" ++
  "  li a0, 0\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_block_hash_matches`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : header_rlp_len
      bytes  8..40 : claimed_block_hash (32 B)
      bytes 40..   : header_rlp
    Output layout:
      bytes  0.. 8 : status (always 0)
      bytes  8..16 : is_valid -/
def ziskBlockHashMatchesPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a1, 8(a7)                # header_rlp_len\n" ++
  "  addi a2, a7, 16             # claimed_hash ptr\n" ++
  "  addi a0, a7, 48             # header_rlp ptr\n" ++
  "  li a3, 0xa0010008           # is_valid out\n" ++
  "  jal ra, block_hash_matches\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lbhm_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  blockHashFromHeaderFunction ++ "\n" ++
  blockHashMatchesFunction ++ "\n" ++
  ".Lbhm_pdone:"

def ziskBlockHashMatchesDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "bhm_computed:\n" ++
  "  .zero 32"

def ziskBlockHashMatchesProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBlockHashMatchesPrologue
  dataAsm     := ziskBlockHashMatchesDataSection
}

/-! ## header_extract_gas_used / header_extract_gas_limit -- PR-K210 / K211

    Two more u64 header-field extractors, completing the
    `header_extract_*` u64 family alongside K198
    (base_fee_per_gas):

      K210  header_extract_gas_used   (field 10)
      K211  header_extract_gas_limit  (field 9)

    Each thin-wraps `rlp_field_to_u64` for the specific field
    index. Useful for chain monitoring / fee-market analysis.

    Calling convention (both):
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp byte length
      a2 (input)  : u64 out ptr
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse failure / field missing
        2 : field exceeds 8 bytes BE -/
def headerExtractGasUsedFunction : String :=
  "header_extract_gas_used:\n" ++
  "  addi sp, sp, -16\n" ++
  "  sd ra, 0(sp)\n" ++
  "  mv a3, a2\n" ++
  "  li a2, 10\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  ld ra, 0(sp)\n" ++
  "  addi sp, sp, 16\n" ++
  "  ret"

def ziskHeaderExtractGasUsedPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a1, 8(a7)\n" ++
  "  addi a0, a7, 16\n" ++
  "  li a2, 0xa0010008\n" ++
  "  jal ra, header_extract_gas_used\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lhegu_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  headerExtractGasUsedFunction ++ "\n" ++
  ".Lhegu_pdone:"

def ziskHeaderExtractGasUsedDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8"

def ziskHeaderExtractGasUsedProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskHeaderExtractGasUsedPrologue
  dataAsm     := ziskHeaderExtractGasUsedDataSection
}

def headerExtractGasLimitFunction : String :=
  "header_extract_gas_limit:\n" ++
  "  addi sp, sp, -16\n" ++
  "  sd ra, 0(sp)\n" ++
  "  mv a3, a2\n" ++
  "  li a2, 9\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  ld ra, 0(sp)\n" ++
  "  addi sp, sp, 16\n" ++
  "  ret"

def ziskHeaderExtractGasLimitPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a1, 8(a7)\n" ++
  "  addi a0, a7, 16\n" ++
  "  li a2, 0xa0010008\n" ++
  "  jal ra, header_extract_gas_limit\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lhegl_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  headerExtractGasLimitFunction ++ "\n" ++
  ".Lhegl_pdone:"

def ziskHeaderExtractGasLimitDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8"

def ziskHeaderExtractGasLimitProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskHeaderExtractGasLimitPrologue
  dataAsm     := ziskHeaderExtractGasLimitDataSection
}

/-! ## block_validate_block_hash_pair -- PR-K212

    Compute both `parent_block_hash` and `child_block_hash`
    AND verify `child.parent_hash == parent_block_hash`. Useful
    for chain-commitment proofs that need both hashes alongside
    the validity bit.

    Composes K172 `block_hash_from_header` (parent + child) +
    K20 `rlp_list_nth_item` (extract child.parent_hash).

    Calling convention:
      a0 (input)  : parent_rlp ptr
      a1 (input)  : parent_rlp byte length
      a2 (input)  : child_rlp ptr
      a3 (input)  : child_rlp byte length
      a4 (input)  : 32-byte output ptr (parent_block_hash)
      a5 (input)  : 32-byte output ptr (child_block_hash)
      a6 (input)  : u64 out (is_valid: 1 if child.parent_hash
                              == parent_block_hash, else 0)
      ra (input)  : return
      a0 (output) :
        0 : success -- both hashes + predicate written
        1 : child RLP parse failure / field 0 missing
        2 : child.parent_hash length != 32 -/
def blockValidateBlockHashPairFunction : String :=
  "block_validate_block_hash_pair:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a0; mv s1, a1                # parent\n" ++
  "  mv s2, a2; mv s3, a3                # child\n" ++
  "  mv s4, a4                            # parent_hash out\n" ++
  "  mv s5, a5                            # child_hash out\n" ++
  "  mv s6, a6                            # is_valid out\n" ++
  "  sd zero, 0(s6)\n" ++
  "  # 1. Compute parent block_hash -> s4\n" ++
  "  mv a0, s0; mv a1, s1; mv a2, s4\n" ++
  "  jal ra, block_hash_from_header\n" ++
  "  # 2. Compute child block_hash -> s5\n" ++
  "  mv a0, s2; mv a1, s3; mv a2, s5\n" ++
  "  jal ra, block_hash_from_header\n" ++
  "  # 3. Extract child.field[0] (parent_hash)\n" ++
  "  mv a0, s2; mv a1, s3; li a2, 0\n" ++
  "  la a3, bvhp_offset; la a4, bvhp_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbvhp_parse_fail\n" ++
  "  la t0, bvhp_length; ld t1, 0(t0)\n" ++
  "  li t2, 32\n" ++
  "  bne t1, t2, .Lbvhp_size_fail\n" ++
  "  # 4. Compare child.parent_hash bytes against s4 (parent_hash)\n" ++
  "  la t0, bvhp_offset; ld t1, 0(t0)\n" ++
  "  add t3, s2, t1\n" ++
  "  ld t4,  0(t3); ld t5,  0(s4); bne t4, t5, .Lbvhp_neq\n" ++
  "  ld t4,  8(t3); ld t5,  8(s4); bne t4, t5, .Lbvhp_neq\n" ++
  "  ld t4, 16(t3); ld t5, 16(s4); bne t4, t5, .Lbvhp_neq\n" ++
  "  ld t4, 24(t3); ld t5, 24(s4); bne t4, t5, .Lbvhp_neq\n" ++
  "  li t0, 1\n" ++
  "  sd t0, 0(s6)\n" ++
  ".Lbvhp_neq:\n" ++
  "  li a0, 0\n" ++
  "  j .Lbvhp_ret\n" ++
  ".Lbvhp_parse_fail:\n" ++
  "  li a0, 1\n" ++
  "  j .Lbvhp_ret\n" ++
  ".Lbvhp_size_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lbvhp_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-- `zisk_block_validate_block_hash_pair`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : parent_rlp_len
      bytes  8..16 : child_rlp_len
      bytes 16..   : parent_rlp || child_rlp
    Output layout:
      bytes  0.. 8 : status
      bytes  8..16 : is_valid
      bytes 16..48 : parent_block_hash
      bytes 48..80 : child_block_hash -/
def ziskBlockValidateBlockHashPairPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a1, 8(a7)                # parent_len\n" ++
  "  ld a3, 16(a7)               # child_len\n" ++
  "  addi a0, a7, 24             # parent_rlp ptr\n" ++
  "  add a2, a0, a1              # child_rlp ptr\n" ++
  "  li a4, 0xa0010010           # parent_hash out\n" ++
  "  li a5, 0xa0010030           # child_hash out\n" ++
  "  li a6, 0xa0010008           # is_valid out\n" ++
  "  jal ra, block_validate_block_hash_pair\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lbvhp_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  zkvmKeccak256Function ++ "\n" ++
  blockHashFromHeaderFunction ++ "\n" ++
  blockValidateBlockHashPairFunction ++ "\n" ++
  ".Lbvhp_pdone:"

def ziskBlockValidateBlockHashPairDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "bvhp_offset:\n" ++
  "  .zero 8\n" ++
  "bvhp_length:\n" ++
  "  .zero 8"

def ziskBlockValidateBlockHashPairProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBlockValidateBlockHashPairPrologue
  dataAsm     := ziskBlockValidateBlockHashPairDataSection
}

/-! ## block_hash_and_extract_number -- PR-K213

    From a single header RLP, return both the block_hash (K172)
    and the block number (field 8 as u64). Useful as the
    "labelled block hash" primitive -- callers commonly want
    both together for chain indexing / commitment.

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp byte length
      a2 (input)  : 32-byte output ptr (block_hash)
      a3 (input)  : u64 out (block number)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse failure / field 8 missing
        2 : number field exceeds 8 bytes BE -/
def blockHashAndExtractNumberFunction : String :=
  "block_hash_and_extract_number:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0; mv s1, a1                # header\n" ++
  "  mv s2, a3                            # number out ptr (stash)\n" ++
  "  # 1. block_hash -> a2 (already set by caller)\n" ++
  "  jal ra, block_hash_from_header\n" ++
  "  # 2. number -> via rlp_field_to_u64(header, len, 8, &out)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 8\n" ++
  "  mv a3, s2\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_block_hash_and_extract_number`: probe BuildUnit.
    Input layout:
      bytes 0..8 : header_rlp_len
      bytes 8..  : header_rlp
    Output layout:
      bytes  0.. 8 : status
      bytes  8..16 : number
      bytes 16..48 : block_hash -/
def ziskBlockHashAndExtractNumberPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a1, 8(a7)                # header_len\n" ++
  "  addi a0, a7, 16             # header ptr\n" ++
  "  li a2, 0xa0010010           # 32B block_hash out\n" ++
  "  li a3, 0xa0010008           # u64 number out\n" ++
  "  jal ra, block_hash_and_extract_number\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lbhen_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  zkvmKeccak256Function ++ "\n" ++
  blockHashFromHeaderFunction ++ "\n" ++
  blockHashAndExtractNumberFunction ++ "\n" ++
  ".Lbhen_pdone:"

def ziskBlockHashAndExtractNumberDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8"

def ziskBlockHashAndExtractNumberProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBlockHashAndExtractNumberPrologue
  dataAsm     := ziskBlockHashAndExtractNumberDataSection
}

end EvmAsm.Codegen
