/-
  EvmAsm.Codegen.Programs.ChainValidate

  Chain-level header validators (predicates returning a
  (valid, bad_index) pair) carved out of
  `EvmAsm.Codegen.Programs.Chain` per the file-size hard cap.
  Hosts:

    K229  chain_validate_increasing_timestamps
    K230  chain_validate_consecutive_numbers
    K240  chain_validate_gas_used_under_limit

  Compose K20 `rlp_list_nth_item` + K34 `rlp_field_to_u64` from
  `RlpRead.lean` + `Tx.lean`. `ChainValidate.lean` imports both.

  No proofs yet -- these are codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.Tx

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## chain_validate_increasing_timestamps -- PR-K229

    Verify that an N-element header chain has strictly
    increasing `timestamp` fields: `headers[i+1].timestamp >
    headers[i].timestamp` for every adjacent pair. Pure
    timestamp-only check; no parent_hash / number / gas_limit
    invariants. The K174 pair check enforces this as part of
    the four-invariant bundle -- K229 is the tight standalone.

    Vacuous-true on N <= 1.

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
        2 : timestamp field > 8 bytes BE on some header -/
def chainValidateIncreasingTimestampsFunction : String :=
  "chain_validate_increasing_timestamps:\n" ++
  "  addi sp, sp, -56\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3; mv s4, a4\n" ++
  "  li t0, 1\n" ++
  "  sd t0, 0(s3); sd zero, 0(s4)\n" ++
  "  li t0, 2\n" ++
  "  bltu s0, t0, .Lcvit_done\n" ++
  "  # Extract headers[0].timestamp into s5 (prev_ts)\n" ++
  "  ld a1, 0(s1)\n" ++
  "  mv a0, s2\n" ++
  "  li a2, 11\n" ++
  "  la a3, cvit_ts\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lcvit_propagate\n" ++
  "  la t0, cvit_ts; ld s5, 0(t0)\n" ++
  "  # Walk: parent_ptr = headers[0]; for i in [0, N-1): parent=headers[i], child=headers[i+1]\n" ++
  "  ld t0, 0(s1)\n" ++
  "  add t1, s2, t0              # child_ptr starts at headers[1]\n" ++
  "  li t2, 1                    # i = 1\n" ++
  ".Lcvit_loop:\n" ++
  "  beq t2, s0, .Lcvit_done\n" ++
  "  la t0, cvit_iter_child; sd t1, 0(t0)\n" ++
  "  la t0, cvit_iter_i;     sd t2, 0(t0)\n" ++
  "  la t0, cvit_iter_prev;  sd s5, 0(t0)\n" ++
  "  slli t3, t2, 3\n" ++
  "  add t3, s1, t3\n" ++
  "  ld a1, 0(t3)                # header_len\n" ++
  "  mv a0, t1\n" ++
  "  li a2, 11\n" ++
  "  la a3, cvit_ts\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lcvit_propagate\n" ++
  "  la t0, cvit_ts;          ld t3, 0(t0)\n" ++
  "  la t0, cvit_iter_prev;   ld t4, 0(t0)\n" ++
  "  bgeu t4, t3, .Lcvit_pred_false\n" ++
  "  # advance\n" ++
  "  la t0, cvit_iter_child;  ld t1, 0(t0)\n" ++
  "  la t0, cvit_iter_i;      ld t2, 0(t0)\n" ++
  "  mv s5, t3                   # prev_ts = current\n" ++
  "  slli t5, t2, 3\n" ++
  "  add t5, s1, t5\n" ++
  "  ld t6, 0(t5)\n" ++
  "  add t1, t1, t6\n" ++
  "  addi t2, t2, 1\n" ++
  "  j .Lcvit_loop\n" ++
  ".Lcvit_pred_false:\n" ++
  "  sd zero, 0(s3)\n" ++
  "  la t0, cvit_iter_i; ld t1, 0(t0)\n" ++
  "  sd t1, 0(s4)\n" ++
  "  li a0, 0\n" ++
  "  j .Lcvit_ret\n" ++
  ".Lcvit_propagate:\n" ++
  "  la t0, cvit_iter_i; ld t1, 0(t0)\n" ++
  "  sd t1, 0(s4)\n" ++
  "  j .Lcvit_ret\n" ++
  ".Lcvit_done:\n" ++
  "  li a0, 0\n" ++
  ".Lcvit_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp)\n" ++
  "  addi sp, sp, 56\n" ++
  "  ret"

def ziskChainValidateIncreasingTimestampsPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a0, 8(a7)\n" ++
  "  addi a1, a7, 16\n" ++
  "  slli t0, a0, 3\n" ++
  "  add a2, a1, t0\n" ++
  "  li a3, 0xa0010008\n" ++
  "  li a4, 0xa0010010\n" ++
  "  jal ra, chain_validate_increasing_timestamps\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lcvit_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  chainValidateIncreasingTimestampsFunction ++ "\n" ++
  ".Lcvit_pdone:"

def ziskChainValidateIncreasingTimestampsDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  "cvit_ts:\n" ++
  "  .zero 8\n" ++
  "cvit_iter_child:\n" ++
  "  .zero 8\n" ++
  "cvit_iter_i:\n" ++
  "  .zero 8\n" ++
  "cvit_iter_prev:\n" ++
  "  .zero 8"

def ziskChainValidateIncreasingTimestampsProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskChainValidateIncreasingTimestampsPrologue
  dataAsm     := ziskChainValidateIncreasingTimestampsDataSection
}

/-! ## chain_validate_consecutive_numbers -- PR-K230

    Verify the chain has strictly consecutive block numbers:
    `headers[i+1].number == headers[i].number + 1`. Pure
    number-only check; analogue of K229 for the `number` field
    (field 8) instead of `timestamp` (field 11), and with `==
    prev + 1` instead of `> prev`.

    Vacuous-true on N <= 1.

    Calling convention:
      a0 (input)  : N
      a1 (input)  : header_lengths ptr
      a2 (input)  : headers ptr
      a3 (input)  : u64 out (is_valid)
      a4 (input)  : u64 out (first_bad_index)
      ra (input)  : return
      a0 (output) :
        0 : success
        1 : RLP parse failure
        2 : number field > 8 bytes BE -/
def chainValidateConsecutiveNumbersFunction : String :=
  "chain_validate_consecutive_numbers:\n" ++
  "  addi sp, sp, -56\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3; mv s4, a4\n" ++
  "  li t0, 1\n" ++
  "  sd t0, 0(s3); sd zero, 0(s4)\n" ++
  "  li t0, 2\n" ++
  "  bltu s0, t0, .Lcvcn_done\n" ++
  "  # headers[0].number -> s5 (prev_num)\n" ++
  "  ld a1, 0(s1)\n" ++
  "  mv a0, s2; li a2, 8\n" ++
  "  la a3, cvcn_num\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lcvcn_propagate\n" ++
  "  la t0, cvcn_num; ld s5, 0(t0)\n" ++
  "  ld t0, 0(s1)\n" ++
  "  add t1, s2, t0              # child_ptr\n" ++
  "  li t2, 1\n" ++
  ".Lcvcn_loop:\n" ++
  "  beq t2, s0, .Lcvcn_done\n" ++
  "  la t0, cvcn_iter_child; sd t1, 0(t0)\n" ++
  "  la t0, cvcn_iter_i;     sd t2, 0(t0)\n" ++
  "  la t0, cvcn_iter_prev;  sd s5, 0(t0)\n" ++
  "  slli t3, t2, 3\n" ++
  "  add t3, s1, t3\n" ++
  "  ld a1, 0(t3)\n" ++
  "  mv a0, t1; li a2, 8\n" ++
  "  la a3, cvcn_num\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lcvcn_propagate\n" ++
  "  la t0, cvcn_num;        ld t3, 0(t0)\n" ++
  "  la t0, cvcn_iter_prev;  ld t4, 0(t0)\n" ++
  "  addi t4, t4, 1\n" ++
  "  bne t4, t3, .Lcvcn_pred_false\n" ++
  "  la t0, cvcn_iter_child; ld t1, 0(t0)\n" ++
  "  la t0, cvcn_iter_i;     ld t2, 0(t0)\n" ++
  "  mv s5, t3\n" ++
  "  slli t5, t2, 3\n" ++
  "  add t5, s1, t5\n" ++
  "  ld t6, 0(t5)\n" ++
  "  add t1, t1, t6\n" ++
  "  addi t2, t2, 1\n" ++
  "  j .Lcvcn_loop\n" ++
  ".Lcvcn_pred_false:\n" ++
  "  sd zero, 0(s3)\n" ++
  "  la t0, cvcn_iter_i; ld t1, 0(t0)\n" ++
  "  sd t1, 0(s4)\n" ++
  "  li a0, 0\n" ++
  "  j .Lcvcn_ret\n" ++
  ".Lcvcn_propagate:\n" ++
  "  la t0, cvcn_iter_i; ld t1, 0(t0)\n" ++
  "  sd t1, 0(s4)\n" ++
  "  j .Lcvcn_ret\n" ++
  ".Lcvcn_done:\n" ++
  "  li a0, 0\n" ++
  ".Lcvcn_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp)\n" ++
  "  addi sp, sp, 56\n" ++
  "  ret"

def ziskChainValidateConsecutiveNumbersPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a0, 8(a7)\n" ++
  "  addi a1, a7, 16\n" ++
  "  slli t0, a0, 3\n" ++
  "  add a2, a1, t0\n" ++
  "  li a3, 0xa0010008\n" ++
  "  li a4, 0xa0010010\n" ++
  "  jal ra, chain_validate_consecutive_numbers\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lcvcn_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  chainValidateConsecutiveNumbersFunction ++ "\n" ++
  ".Lcvcn_pdone:"

def ziskChainValidateConsecutiveNumbersDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  "cvcn_num:\n" ++
  "  .zero 8\n" ++
  "cvcn_iter_child:\n" ++
  "  .zero 8\n" ++
  "cvcn_iter_i:\n" ++
  "  .zero 8\n" ++
  "cvcn_iter_prev:\n" ++
  "  .zero 8"

def ziskChainValidateConsecutiveNumbersProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskChainValidateConsecutiveNumbersPrologue
  dataAsm     := ziskChainValidateConsecutiveNumbersDataSection
}

/-! ## chain_validate_gas_used_under_limit -- PR-K240

    Per-header invariant: `gas_used <= gas_limit` (header fields
    10 and 9 respectively). The block validator already enforces
    `gas_used <= gas_limit` in K72 `check_gas_limit` for adjacent
    pairs; K240 lifts the standalone per-block constraint to an
    N-element chain.

    Vacuous on empty chain: valid=1, bad_index=0.

    Calling convention:
      a0 (input)  : N
      a1 (input)  : header_lengths ptr (N u64 LE)
      a2 (input)  : flat headers ptr
      a3 (input)  : u64 out (valid: 1 = all OK)
      a4 (input)  : u64 out (bad_index = first violator, else 0)
      ra (input)  : return
      a0 (output) :
        0 : success — predicate written
        1 : RLP parse fail on some header
        2 : gas_used or gas_limit field > 8 bytes BE -/
def chainValidateGasUsedUnderLimitFunction : String :=
  "chain_validate_gas_used_under_limit:\n" ++
  "  addi sp, sp, -56\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3; mv s4, a4\n" ++
  "  li t0, 1\n" ++
  "  sd t0, 0(s3); sd zero, 0(s4)\n" ++
  "  li s5, 0\n" ++
  ".Lcvgul_loop:\n" ++
  "  beq s5, s0, .Lcvgul_done\n" ++
  "  la t0, cvgul_iter_ptr; sd s2, 0(t0)\n" ++
  "  la t0, cvgul_iter_i;   sd s5, 0(t0)\n" ++
  "  slli t3, s5, 3\n" ++
  "  add t3, s1, t3\n" ++
  "  ld a1, 0(t3)\n" ++
  "  mv a0, s2; li a2, 10\n" ++
  "  la a3, cvgul_gas_used\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lcvgul_propagate\n" ++
  "  la t0, cvgul_iter_ptr; ld s2, 0(t0)\n" ++
  "  la t0, cvgul_iter_i;   ld s5, 0(t0)\n" ++
  "  slli t3, s5, 3\n" ++
  "  add t3, s1, t3\n" ++
  "  ld a1, 0(t3)\n" ++
  "  mv a0, s2; li a2, 9\n" ++
  "  la a3, cvgul_gas_limit\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lcvgul_propagate\n" ++
  "  la t0, cvgul_iter_ptr; ld s2, 0(t0)\n" ++
  "  la t0, cvgul_iter_i;   ld s5, 0(t0)\n" ++
  "  la t0, cvgul_gas_used;  ld t1, 0(t0)\n" ++
  "  la t0, cvgul_gas_limit; ld t2, 0(t0)\n" ++
  "  bgtu t1, t2, .Lcvgul_violation\n" ++
  "  slli t3, s5, 3\n" ++
  "  add t3, s1, t3\n" ++
  "  ld t4, 0(t3)\n" ++
  "  add s2, s2, t4\n" ++
  "  addi s5, s5, 1\n" ++
  "  j .Lcvgul_loop\n" ++
  ".Lcvgul_violation:\n" ++
  "  sd zero, 0(s3)\n" ++
  "  sd s5, 0(s4)\n" ++
  "  li a0, 0\n" ++
  "  j .Lcvgul_ret\n" ++
  ".Lcvgul_propagate:\n" ++
  "  sd s5, 0(s4)\n" ++
  "  j .Lcvgul_ret\n" ++
  ".Lcvgul_done:\n" ++
  "  li a0, 0\n" ++
  ".Lcvgul_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp)\n" ++
  "  addi sp, sp, 56\n" ++
  "  ret"

def ziskChainValidateGasUsedUnderLimitPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a0, 8(a7)\n" ++
  "  addi a1, a7, 16\n" ++
  "  slli t0, a0, 3\n" ++
  "  add a2, a1, t0\n" ++
  "  li a3, 0xa0010008\n" ++
  "  li a4, 0xa0010010\n" ++
  "  jal ra, chain_validate_gas_used_under_limit\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lcvgul_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  chainValidateGasUsedUnderLimitFunction ++ "\n" ++
  ".Lcvgul_pdone:"

def ziskChainValidateGasUsedUnderLimitDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  "cvgul_gas_used:\n" ++
  "  .zero 8\n" ++
  "cvgul_gas_limit:\n" ++
  "  .zero 8\n" ++
  "cvgul_iter_ptr:\n" ++
  "  .zero 8\n" ++
  "cvgul_iter_i:\n" ++
  "  .zero 8"

def ziskChainValidateGasUsedUnderLimitProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskChainValidateGasUsedUnderLimitPrologue
  dataAsm     := ziskChainValidateGasUsedUnderLimitDataSection
}

/-! ## chain_validate_no_blob_txs -- PR-K258

    Per-header invariant: every header has `blob_gas_used == 0`
    (field 17 either missing or RLP-empty). Useful for proving a
    chain segment contains no blob-carrying transactions —
    callers wanting to skip blob-fee market evolution use this
    as a short-circuit.

    Field 17 missing (pre-Cancun header) counts as
    blob_gas_used == 0; mixed pre- and post-Cancun chains pass
    as long as no Cancun header actually used blob gas.

    Vacuous on empty chain: valid=1, bad_index=0.

    Calling convention:
      a0 (input)  : N
      a1 (input)  : header_lengths ptr (N u64 LE)
      a2 (input)  : flat headers ptr
      a3 (input)  : u64 out (valid: 1 = all blob_gas_used==0)
      a4 (input)  : u64 out (bad_index = first violator, else 0)
      ra (input)  : return
      a0 (output) :
        0 : success — predicate written
        1 : RLP parse fail on some header (post-Cancun shape error)
        2 : field 17 > 8 bytes BE -/
def chainValidateNoBlobTxsFunction : String :=
  "chain_validate_no_blob_txs:\n" ++
  "  addi sp, sp, -56\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3; mv s4, a4\n" ++
  "  li t0, 1\n" ++
  "  sd t0, 0(s3); sd zero, 0(s4)\n" ++
  "  li s5, 0\n" ++
  ".Lcvnbt_loop:\n" ++
  "  beq s5, s0, .Lcvnbt_done\n" ++
  "  la t0, cvnbt_iter_ptr; sd s2, 0(t0)\n" ++
  "  la t0, cvnbt_iter_i;   sd s5, 0(t0)\n" ++
  "  slli t3, s5, 3\n" ++
  "  add t3, s1, t3\n" ++
  "  ld a1, 0(t3)\n" ++
  "  mv a0, s2; li a2, 17\n" ++
  "  la a3, cvnbt_field\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  la t0, cvnbt_iter_ptr; ld s2, 0(t0)\n" ++
  "  la t0, cvnbt_iter_i;   ld s5, 0(t0)\n" ++
  "  li t0, 1\n" ++
  "  beq a0, t0, .Lcvnbt_no_field\n" ++
  "  li t0, 2\n" ++
  "  beq a0, t0, .Lcvnbt_size_fail\n" ++
  "  la t0, cvnbt_field; ld t1, 0(t0)\n" ++
  "  bnez t1, .Lcvnbt_violation\n" ++
  ".Lcvnbt_no_field:\n" ++
  "  slli t3, s5, 3\n" ++
  "  add t3, s1, t3\n" ++
  "  ld t4, 0(t3)\n" ++
  "  add s2, s2, t4\n" ++
  "  addi s5, s5, 1\n" ++
  "  j .Lcvnbt_loop\n" ++
  ".Lcvnbt_violation:\n" ++
  "  sd zero, 0(s3)\n" ++
  "  sd s5, 0(s4)\n" ++
  "  li a0, 0\n" ++
  "  j .Lcvnbt_ret\n" ++
  ".Lcvnbt_size_fail:\n" ++
  "  sd s5, 0(s4)\n" ++
  "  li a0, 2\n" ++
  "  j .Lcvnbt_ret\n" ++
  ".Lcvnbt_done:\n" ++
  "  li a0, 0\n" ++
  ".Lcvnbt_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp)\n" ++
  "  addi sp, sp, 56\n" ++
  "  ret"

def ziskChainValidateNoBlobTxsPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a0, 8(a7)\n" ++
  "  addi a1, a7, 16\n" ++
  "  slli t0, a0, 3\n" ++
  "  add a2, a1, t0\n" ++
  "  li a3, 0xa0010008\n" ++
  "  li a4, 0xa0010010\n" ++
  "  jal ra, chain_validate_no_blob_txs\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lcvnbt_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  chainValidateNoBlobTxsFunction ++ "\n" ++
  ".Lcvnbt_pdone:"

def ziskChainValidateNoBlobTxsDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  "cvnbt_field:\n" ++
  "  .zero 8\n" ++
  "cvnbt_iter_ptr:\n" ++
  "  .zero 8\n" ++
  "cvnbt_iter_i:\n" ++
  "  .zero 8"

def ziskChainValidateNoBlobTxsProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskChainValidateNoBlobTxsPrologue
  dataAsm     := ziskChainValidateNoBlobTxsDataSection
}

end EvmAsm.Codegen
