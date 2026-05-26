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

/-! ## chain_validate_nonce_zero -- PR-K288

    Per-header invariant: `nonce == 0` (field 14, 8 bytes BE).
    EIP-3675 / the Merge mandates the 8-byte nonce field is
    zero in every post-merge header. Companion to K287
    chain_validate_difficulty_zero.

    Useful as a `is-post-merge-segment` predicate for analytics
    windows; both K287 and K288 together cleanly characterize a
    post-merge chain segment.

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
        2 : nonce field > 8 bytes BE on some header -/
def chainValidateNonceZeroFunction : String :=
  "chain_validate_nonce_zero:\n" ++
  "  addi sp, sp, -56\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3; mv s4, a4\n" ++
  "  li t0, 1\n" ++
  "  sd t0, 0(s3); sd zero, 0(s4)\n" ++
  "  li s5, 0\n" ++
  ".Lcvnz_loop:\n" ++
  "  beq s5, s0, .Lcvnz_done\n" ++
  "  la t0, cvnz_iter_ptr; sd s2, 0(t0)\n" ++
  "  la t0, cvnz_iter_i;   sd s5, 0(t0)\n" ++
  "  slli t3, s5, 3\n" ++
  "  add t3, s1, t3\n" ++
  "  ld a1, 0(t3)\n" ++
  "  mv a0, s2; li a2, 14\n" ++
  "  la a3, cvnz_field\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lcvnz_propagate\n" ++
  "  la t0, cvnz_iter_ptr; ld s2, 0(t0)\n" ++
  "  la t0, cvnz_iter_i;   ld s5, 0(t0)\n" ++
  "  la t0, cvnz_field;    ld t1, 0(t0)\n" ++
  "  bnez t1, .Lcvnz_violation\n" ++
  "  slli t3, s5, 3\n" ++
  "  add t3, s1, t3\n" ++
  "  ld t4, 0(t3)\n" ++
  "  add s2, s2, t4\n" ++
  "  addi s5, s5, 1\n" ++
  "  j .Lcvnz_loop\n" ++
  ".Lcvnz_violation:\n" ++
  "  sd zero, 0(s3)\n" ++
  "  sd s5, 0(s4)\n" ++
  "  li a0, 0\n" ++
  "  j .Lcvnz_ret\n" ++
  ".Lcvnz_propagate:\n" ++
  "  sd s5, 0(s4)\n" ++
  "  j .Lcvnz_ret\n" ++
  ".Lcvnz_done:\n" ++
  "  li a0, 0\n" ++
  ".Lcvnz_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp)\n" ++
  "  addi sp, sp, 56\n" ++
  "  ret"

def ziskChainValidateNonceZeroPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a0, 8(a7)\n" ++
  "  addi a1, a7, 16\n" ++
  "  slli t0, a0, 3\n" ++
  "  add a2, a1, t0\n" ++
  "  li a3, 0xa0010008\n" ++
  "  li a4, 0xa0010010\n" ++
  "  jal ra, chain_validate_nonce_zero\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lcvnz_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  chainValidateNonceZeroFunction ++ "\n" ++
  ".Lcvnz_pdone:"

def ziskChainValidateNonceZeroDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  "cvnz_field:\n" ++
  "  .zero 8\n" ++
  "cvnz_iter_ptr:\n" ++
  "  .zero 8\n" ++
  "cvnz_iter_i:\n" ++
  "  .zero 8"

def ziskChainValidateNonceZeroProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskChainValidateNonceZeroPrologue
  dataAsm     := ziskChainValidateNonceZeroDataSection
}

/-! ## chain_validate_ommers_hash_empty -- PR-K289

    Per-header invariant: `ommers_hash == EMPTY_LIST_KECCAK`
    (header field 1) where
    `EMPTY_LIST_KECCAK = keccak256(rlp([])) =
     0x1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347`.
    EIP-3675 / the Merge eliminated uncle blocks; every
    post-merge header has an empty ommers list and thus this
    fixed 32-byte hash.

    Companion to K287 chain_validate_difficulty_zero and K288
    chain_validate_nonce_zero; the three together fully
    characterize a post-merge chain segment.

    Vacuous-true on N = 0. Uses byte-wise word comparison
    against the embedded constant in .data.

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
        2 : ommers_hash field length != 32 on some header -/
def chainValidateOmmersHashEmptyFunction : String :=
  "chain_validate_ommers_hash_empty:\n" ++
  "  addi sp, sp, -56\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3; mv s4, a4\n" ++
  "  li t0, 1\n" ++
  "  sd t0, 0(s3); sd zero, 0(s4)\n" ++
  "  li s5, 0\n" ++
  ".Lcvohe_loop:\n" ++
  "  beq s5, s0, .Lcvohe_done\n" ++
  "  la t0, cvohe_iter_ptr; sd s2, 0(t0)\n" ++
  "  la t0, cvohe_iter_i;   sd s5, 0(t0)\n" ++
  "  slli t3, s5, 3\n" ++
  "  add t3, s1, t3\n" ++
  "  ld a1, 0(t3)\n" ++
  "  mv a0, s2; li a2, 1\n" ++
  "  la a3, cvohe_offset; la a4, cvohe_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lcvohe_propagate\n" ++
  "  la t0, cvohe_length; ld t1, 0(t0)\n" ++
  "  li t2, 32\n" ++
  "  bne t1, t2, .Lcvohe_size_fail\n" ++
  "  la t0, cvohe_iter_ptr; ld s2, 0(t0)\n" ++
  "  la t0, cvohe_iter_i;   ld s5, 0(t0)\n" ++
  "  la t0, cvohe_offset; ld t1, 0(t0)\n" ++
  "  add t2, s2, t1                # t2 = ptr to ommers_hash bytes\n" ++
  "  la t3, cvohe_empty_hash\n" ++
  "  ld t4,  0(t2); ld t5,  0(t3); bne t4, t5, .Lcvohe_violation\n" ++
  "  ld t4,  8(t2); ld t5,  8(t3); bne t4, t5, .Lcvohe_violation\n" ++
  "  ld t4, 16(t2); ld t5, 16(t3); bne t4, t5, .Lcvohe_violation\n" ++
  "  ld t4, 24(t2); ld t5, 24(t3); bne t4, t5, .Lcvohe_violation\n" ++
  "  slli t3, s5, 3\n" ++
  "  add t3, s1, t3\n" ++
  "  ld t4, 0(t3)\n" ++
  "  add s2, s2, t4\n" ++
  "  addi s5, s5, 1\n" ++
  "  j .Lcvohe_loop\n" ++
  ".Lcvohe_violation:\n" ++
  "  sd zero, 0(s3)\n" ++
  "  sd s5, 0(s4)\n" ++
  "  li a0, 0\n" ++
  "  j .Lcvohe_ret\n" ++
  ".Lcvohe_size_fail:\n" ++
  "  la t0, cvohe_iter_i; ld t1, 0(t0)\n" ++
  "  sd t1, 0(s4)\n" ++
  "  li a0, 2\n" ++
  "  j .Lcvohe_ret\n" ++
  ".Lcvohe_propagate:\n" ++
  "  sd s5, 0(s4)\n" ++
  "  li a0, 1\n" ++
  "  j .Lcvohe_ret\n" ++
  ".Lcvohe_done:\n" ++
  "  li a0, 0\n" ++
  ".Lcvohe_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp)\n" ++
  "  addi sp, sp, 56\n" ++
  "  ret"

def ziskChainValidateOmmersHashEmptyPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a0, 8(a7)\n" ++
  "  addi a1, a7, 16\n" ++
  "  slli t0, a0, 3\n" ++
  "  add a2, a1, t0\n" ++
  "  li a3, 0xa0010008\n" ++
  "  li a4, 0xa0010010\n" ++
  "  jal ra, chain_validate_ommers_hash_empty\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lcvohe_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  chainValidateOmmersHashEmptyFunction ++ "\n" ++
  ".Lcvohe_pdone:"

def ziskChainValidateOmmersHashEmptyDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "cvohe_offset:\n" ++
  "  .zero 8\n" ++
  "cvohe_length:\n" ++
  "  .zero 8\n" ++
  "cvohe_iter_ptr:\n" ++
  "  .zero 8\n" ++
  "cvohe_iter_i:\n" ++
  "  .zero 8\n" ++
  "cvohe_empty_hash:\n" ++
  "  .byte 0x1d, 0xcc, 0x4d, 0xe8, 0xde, 0xc7, 0x5d, 0x7a\n" ++
  "  .byte 0xab, 0x85, 0xb5, 0x67, 0xb6, 0xcc, 0xd4, 0x1a\n" ++
  "  .byte 0xd3, 0x12, 0x45, 0x1b, 0x94, 0x8a, 0x74, 0x13\n" ++
  "  .byte 0xf0, 0xa1, 0x42, 0xfd, 0x40, 0xd4, 0x93, 0x47"

def ziskChainValidateOmmersHashEmptyProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskChainValidateOmmersHashEmptyPrologue
  dataAsm     := ziskChainValidateOmmersHashEmptyDataSection
}

end EvmAsm.Codegen
