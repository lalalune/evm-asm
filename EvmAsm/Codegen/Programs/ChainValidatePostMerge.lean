/-
  EvmAsm.Codegen.Programs.ChainValidatePostMerge

  Post-merge (EIP-3675) chain-level invariants, carved out of
  `Programs.ChainValidate` per the file-size hard cap. Hosts:

    K287  chain_validate_difficulty_zero

  Future EIP-3675-only predicates (e.g. nonce_zero,
  ommers_hash_empty_uncle_list) will land here.

  All predicates compose K20 `rlp_list_nth_item` + K34
  `rlp_field_to_u64` helpers, shared with the rest of the
  validators.

  No proofs yet -- these are codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.Tx

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## chain_validate_difficulty_zero -- PR-K287

    Per-header invariant: `difficulty == 0` (field 7). EIP-3675
    (the Merge) deprecated PoW and forced `difficulty = 0` for
    every post-merge block. Useful as a `is-post-merge-segment`
    predicate for analytics windows.

    Note: when `difficulty == 0`, RLP encodes the integer as an
    empty byte string; `rlp_field_to_u64` returns 0. Any nonzero
    value (whether single-byte or multi-byte BE encoding) flags
    a violation.

    Vacuous-true on N = 0.

    Calling convention:
      a0 (input)  : N (header count)
      a1 (input)  : header_lengths ptr
      a2 (input)  : headers ptr (concatenated)
      a3 (input)  : u64 out (is_valid)
      a4 (input)  : u64 out (first_bad_index)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse failure on some header
        2 : difficulty field > 8 bytes BE on some header -/
def chainValidateDifficultyZeroFunction : String :=
  "chain_validate_difficulty_zero:\n" ++
  "  addi sp, sp, -56\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3; mv s4, a4\n" ++
  "  li t0, 1\n" ++
  "  sd t0, 0(s3); sd zero, 0(s4)\n" ++
  "  li s5, 0\n" ++
  ".Lcvdz_loop:\n" ++
  "  beq s5, s0, .Lcvdz_done\n" ++
  "  la t0, cvdz_iter_ptr; sd s2, 0(t0)\n" ++
  "  la t0, cvdz_iter_i;   sd s5, 0(t0)\n" ++
  "  slli t3, s5, 3\n" ++
  "  add t3, s1, t3\n" ++
  "  ld a1, 0(t3)\n" ++
  "  mv a0, s2; li a2, 7\n" ++
  "  la a3, cvdz_field\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lcvdz_propagate\n" ++
  "  la t0, cvdz_iter_ptr; ld s2, 0(t0)\n" ++
  "  la t0, cvdz_iter_i;   ld s5, 0(t0)\n" ++
  "  la t0, cvdz_field;    ld t1, 0(t0)\n" ++
  "  bnez t1, .Lcvdz_violation\n" ++
  "  slli t3, s5, 3\n" ++
  "  add t3, s1, t3\n" ++
  "  ld t4, 0(t3)\n" ++
  "  add s2, s2, t4\n" ++
  "  addi s5, s5, 1\n" ++
  "  j .Lcvdz_loop\n" ++
  ".Lcvdz_violation:\n" ++
  "  sd zero, 0(s3)\n" ++
  "  sd s5, 0(s4)\n" ++
  "  li a0, 0\n" ++
  "  j .Lcvdz_ret\n" ++
  ".Lcvdz_propagate:\n" ++
  "  sd s5, 0(s4)\n" ++
  "  j .Lcvdz_ret\n" ++
  ".Lcvdz_done:\n" ++
  "  li a0, 0\n" ++
  ".Lcvdz_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp)\n" ++
  "  addi sp, sp, 56\n" ++
  "  ret"

def ziskChainValidateDifficultyZeroPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a0, 8(a7)\n" ++
  "  addi a1, a7, 16\n" ++
  "  slli t0, a0, 3\n" ++
  "  add a2, a1, t0\n" ++
  "  li a3, 0xa0010008\n" ++
  "  li a4, 0xa0010010\n" ++
  "  jal ra, chain_validate_difficulty_zero\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lcvdz_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  chainValidateDifficultyZeroFunction ++ "\n" ++
  ".Lcvdz_pdone:"

def ziskChainValidateDifficultyZeroDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  "cvdz_field:\n" ++
  "  .zero 8\n" ++
  "cvdz_iter_ptr:\n" ++
  "  .zero 8\n" ++
  "cvdz_iter_i:\n" ++
  "  .zero 8"

def ziskChainValidateDifficultyZeroProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskChainValidateDifficultyZeroPrologue
  dataAsm     := ziskChainValidateDifficultyZeroDataSection
}

end EvmAsm.Codegen
