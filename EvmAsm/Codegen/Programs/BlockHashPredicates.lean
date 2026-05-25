/-
  EvmAsm.Codegen.Programs.BlockHashPredicates

  Per-block hash predicates + companion extractors carved out of
  `EvmAsm.Codegen.Programs.Header` per the file-size hard cap.
  Hosts:

    K209  block_hash_matches
    K210  header_extract_gas_used
    K211  header_extract_gas_limit
    K212  block_validate_block_hash_pair
    K213  block_hash_and_extract_number
    K214  header_compute_summary_struct

  Compose K172 `block_hash_from_header` (Header.lean), K201
  `header_extract_state_root` (HeaderFields.lean), K20 / K34 from
  RlpRead + Tx, and `zkvm_keccak256` from HashBridge.

  No proofs yet -- these are codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.Tx
import EvmAsm.Codegen.Programs.Header
import EvmAsm.Codegen.Programs.HeaderFields

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

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

/-! ## header_compute_summary_struct -- PR-K214

    Extract a 96-byte block summary struct from a header:

      bytes  0.. 32 : block_hash         (keccak256 of header RLP)
      bytes 32.. 64 : state_root         (field 3)
      bytes 64.. 72 : number             (field 8, u64)
      bytes 72.. 80 : timestamp          (field 11, u64)
      bytes 80.. 88 : gas_used           (field 10, u64)
      bytes 88.. 96 : base_fee_per_gas   (field 15, u64; pre-
                                          London headers fail
                                          and the field stays 0)

    Useful as a chain-indexing primitive: stores the canonical
    "what is this block" tuple in one shot, ready to dump as a
    fixed-size record.

    Composes K172 (block_hash) + K201 (state_root) +
    rlp_field_to_u64 ×4. The integer fields use the same shape
    as K198 / K210 / K211 / K38; the state_root copy uses the
    same 4 × 8B pattern as K201.

    Calling convention:
      a0 (input)  : header_rlp ptr
      a1 (input)  : header_rlp byte length
      a2 (input)  : 96-byte output ptr
      ra (input)  : return
      a0 (output) :
        0 : success (all 6 fields written)
        1 : RLP parse failure / required field missing
        2 : some integer field exceeds 8 bytes BE / state_root != 32 -/
def headerComputeSummaryStructFunction : String :=
  "header_compute_summary_struct:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0; mv s1, a1                # header\n" ++
  "  mv s2, a2                            # output struct\n" ++
  "  # 1. block_hash -> out[0..32]\n" ++
  "  mv a0, s0; mv a1, s1; mv a2, s2\n" ++
  "  jal ra, block_hash_from_header\n" ++
  "  # 2. state_root -> out[32..64]\n" ++
  "  mv a0, s0; mv a1, s1\n" ++
  "  addi a2, s2, 32\n" ++
  "  jal ra, header_extract_state_root\n" ++
  "  bnez a0, .Lhcss_propagate_size\n" ++
  "  # 3. number -> out[64..72] (field 8)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 8\n" ++
  "  addi a3, s2, 64\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lhcss_propagate_int\n" ++
  "  # 4. timestamp -> out[72..80] (field 11)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 11\n" ++
  "  addi a3, s2, 72\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lhcss_propagate_int\n" ++
  "  # 5. gas_used -> out[80..88] (field 10)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 10\n" ++
  "  addi a3, s2, 80\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lhcss_propagate_int\n" ++
  "  # 6. base_fee_per_gas -> out[88..96] (field 15)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 15\n" ++
  "  addi a3, s2, 88\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lhcss_propagate_int\n" ++
  "  li a0, 0\n" ++
  "  j .Lhcss_ret\n" ++
  ".Lhcss_propagate_size:\n" ++
  "  # state_root status: 1=parse, 2=size. Pass through unchanged.\n" ++
  "  j .Lhcss_ret\n" ++
  ".Lhcss_propagate_int:\n" ++
  "  # rlp_field_to_u64 returns 1=parse, 2=too_long. Map both to\n" ++
  "  # the same code as the upper-level status.\n" ++
  ".Lhcss_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- `zisk_header_compute_summary_struct`: probe BuildUnit.
    Input layout:
      bytes 0..8 : header_rlp_len
      bytes 8..  : header_rlp
    Output layout:
      bytes  0.. 8 : status
      bytes  8..104: 96-byte summary struct -/
def ziskHeaderComputeSummaryStructPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a1, 8(a7)\n" ++
  "  addi a0, a7, 16\n" ++
  "  li a2, 0xa0010008\n" ++
  "  jal ra, header_compute_summary_struct\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lhcss_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  zkvmKeccak256Function ++ "\n" ++
  blockHashFromHeaderFunction ++ "\n" ++
  headerExtractStateRootFunction ++ "\n" ++
  headerComputeSummaryStructFunction ++ "\n" ++
  ".Lhcss_pdone:"

def ziskHeaderComputeSummaryStructDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  "hesr_offset:\n" ++
  "  .zero 8\n" ++
  "hesr_length:\n" ++
  "  .zero 8"

def ziskHeaderComputeSummaryStructProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskHeaderComputeSummaryStructPrologue
  dataAsm     := ziskHeaderComputeSummaryStructDataSection
}


end EvmAsm.Codegen
