/-
  EvmAsm.Codegen.Programs.ChainValidateBlob

  Blob-related chain-level validators (header fields 17/18,
  Cancun+), carved out of `Programs.ChainValidate` per the
  file-size hard cap. Hosts:

    K274  chain_validate_excess_blob_gas_non_decreasing

  Sister modules for non-blob chain validators stay in
  `Programs.ChainValidate` (timestamps / numbers / gas_used /
  gas_limit / basefee). Future Cancun+ predicates over fields 17
  / 18 / 19 land here.

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

/-! ## chain_validate_excess_blob_gas_non_decreasing -- PR-K274

    Per-pair invariant: `excess_blob_gas[i] <= excess_blob_gas[i+1]`
    for all 0 <= i < N-1 (header field 18, Cancun+). Useful for
    spotting sustained over-target blob windows where the running
    counter grows monotonically.

    Mirrors K267 chain_validate_basefee_non_decreasing in shape;
    differs by field (18 vs 15).

    Pre-Cancun headers (<19 fields) raise parse-failure status.

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
        2 : excess_blob_gas field > 8 bytes BE on some header -/
def chainValidateExcessBlobGasNonDecreasingFunction : String :=
  "chain_validate_excess_blob_gas_non_decreasing:\n" ++
  "  addi sp, sp, -56\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3; mv s4, a4\n" ++
  "  li t0, 1\n" ++
  "  sd t0, 0(s3); sd zero, 0(s4)\n" ++
  "  li t0, 2\n" ++
  "  bltu s0, t0, .Lcvebnd_done\n" ++
  "  # Extract headers[0].excess_blob_gas into s5 (prev)\n" ++
  "  ld a1, 0(s1)\n" ++
  "  mv a0, s2\n" ++
  "  li a2, 18\n" ++
  "  la a3, cvebnd_field\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lcvebnd_propagate\n" ++
  "  la t0, cvebnd_field; ld s5, 0(t0)\n" ++
  "  ld t0, 0(s1)\n" ++
  "  add t1, s2, t0\n" ++
  "  li t2, 1\n" ++
  ".Lcvebnd_loop:\n" ++
  "  beq t2, s0, .Lcvebnd_done\n" ++
  "  la t0, cvebnd_iter_child; sd t1, 0(t0)\n" ++
  "  la t0, cvebnd_iter_i;     sd t2, 0(t0)\n" ++
  "  la t0, cvebnd_iter_prev;  sd s5, 0(t0)\n" ++
  "  slli t3, t2, 3\n" ++
  "  add t3, s1, t3\n" ++
  "  ld a1, 0(t3)\n" ++
  "  mv a0, t1\n" ++
  "  li a2, 18\n" ++
  "  la a3, cvebnd_field\n" ++
  "  jal ra, rlp_field_to_u64\n" ++
  "  bnez a0, .Lcvebnd_propagate\n" ++
  "  la t0, cvebnd_field;        ld t3, 0(t0)\n" ++
  "  la t0, cvebnd_iter_prev;    ld t4, 0(t0)\n" ++
  "  bltu t3, t4, .Lcvebnd_pred_false\n" ++
  "  la t0, cvebnd_iter_child;   ld t1, 0(t0)\n" ++
  "  la t0, cvebnd_iter_i;       ld t2, 0(t0)\n" ++
  "  mv s5, t3\n" ++
  "  slli t5, t2, 3\n" ++
  "  add t5, s1, t5\n" ++
  "  ld t6, 0(t5)\n" ++
  "  add t1, t1, t6\n" ++
  "  addi t2, t2, 1\n" ++
  "  j .Lcvebnd_loop\n" ++
  ".Lcvebnd_pred_false:\n" ++
  "  sd zero, 0(s3)\n" ++
  "  la t0, cvebnd_iter_i; ld t1, 0(t0)\n" ++
  "  sd t1, 0(s4)\n" ++
  "  li a0, 0\n" ++
  "  j .Lcvebnd_ret\n" ++
  ".Lcvebnd_propagate:\n" ++
  "  la t0, cvebnd_iter_i; ld t1, 0(t0)\n" ++
  "  sd t1, 0(s4)\n" ++
  "  j .Lcvebnd_ret\n" ++
  ".Lcvebnd_done:\n" ++
  "  li a0, 0\n" ++
  ".Lcvebnd_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp)\n" ++
  "  addi sp, sp, 56\n" ++
  "  ret"

def ziskChainValidateExcessBlobGasNonDecreasingPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld a0, 8(a7)\n" ++
  "  addi a1, a7, 16\n" ++
  "  slli t0, a0, 3\n" ++
  "  add a2, a1, t0\n" ++
  "  li a3, 0xa0010008\n" ++
  "  li a4, 0xa0010010\n" ++
  "  jal ra, chain_validate_excess_blob_gas_non_decreasing\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lcvebnd_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  chainValidateExcessBlobGasNonDecreasingFunction ++ "\n" ++
  ".Lcvebnd_pdone:"

def ziskChainValidateExcessBlobGasNonDecreasingDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  "rfu_offset:\n" ++
  "  .zero 8\n" ++
  "rfu_length:\n" ++
  "  .zero 8\n" ++
  "cvebnd_field:\n" ++
  "  .zero 8\n" ++
  "cvebnd_iter_child:\n" ++
  "  .zero 8\n" ++
  "cvebnd_iter_i:\n" ++
  "  .zero 8\n" ++
  "cvebnd_iter_prev:\n" ++
  "  .zero 8"

def ziskChainValidateExcessBlobGasNonDecreasingProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskChainValidateExcessBlobGasNonDecreasingPrologue
  dataAsm     := ziskChainValidateExcessBlobGasNonDecreasingDataSection
}

end EvmAsm.Codegen
