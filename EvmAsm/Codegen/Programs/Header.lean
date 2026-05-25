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
import EvmAsm.Codegen.Programs.HeaderFields

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

/-! ## K201..K208 single-field extractors -- moved to Programs/HeaderFields.lean (file-size hard cap). -/

/-! ## header_extract_timestamp -- PR-K232

    Extract `timestamp` (field 11, u64 BE) from a header RLP.
    Cross-fork — every header has timestamp.

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp byte length
      a2 (input)  : u64 out ptr
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse failure
        2 : field 11 exceeds 8 bytes BE -/
def headerExtractTimestampFunction : String :=
  "header_extract_timestamp:\n" ++
  "  addi sp, sp, -16\n" ++
  "  sd ra, 0(sp)\n" ++
  "  mv a3, a2\n" ++
  "  li a2, 11\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  ld ra, 0(sp)\n" ++
  "  addi sp, sp, 16\n" ++
  "  ret"

def ziskHeaderExtractTimestampPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a1, 8(a7)\n" ++
  "  addi a0, a7, 16\n" ++
  "  li a2, 0xa0010008\n" ++
  "  jal ra, header_extract_timestamp\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lhets_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  headerExtractTimestampFunction ++ "\n" ++
  ".Lhets_pdone:"

def ziskHeaderExtractTimestampDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8"

def ziskHeaderExtractTimestampProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskHeaderExtractTimestampPrologue
  dataAsm     := ziskHeaderExtractTimestampDataSection
}

end EvmAsm.Codegen
