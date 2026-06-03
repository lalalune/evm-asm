/-
  EvmAsm.Codegen.Programs.BlockRlpSize

  RISC-V helpers for EIP-7934 block RLP size enforcement. The main helper
  computes the exact canonical `len(rlp.encode(Block(...)))` from the SSZ
  ExecutionPayload shape consumed by the stateless guest, plus the caller's
  already rebuilt header RLP length. This assumes the stateless input represents
  the same block that execution-specs validates; see
  `docs/execution-specs-feedback.md` for the EIP-7934 fixture-equivalence note.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Programs.BalGasValid
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.Withdrawal

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## block_rlp_rebuilt_size -- compute len(rlp.encode(Block(...))) from SSZ.
    Mirrors execution-specs' EIP-7934 check without trusting fixture sidecars:
    the caller supplies the already rebuilt header RLP length, and this routine
    derives the transaction and withdrawal list RLP lengths from the SSZ
    ExecutionPayload. It returns status in a0 and rebuilt block RLP length in a1.

    a0 = SSZ ExecutionPayload ptr   a1 = rebuilt header RLP length
    a2 = SSZ_BASE                   a0 = 0 ok / 1 malformed input, a1 = length -/
def rlpBytesEncodedSizeFunction : String :=
  "rlp_bytes_encoded_size:\n" ++
  "  li t0, 1\n" ++
  "  bne a1, t0, .Lrbes_not_single\n" ++
  "  lbu t1, 0(a0); li t2, 0x80; bltu t1, t2, .Lrbes_single_raw\n" ++
  ".Lrbes_not_single:\n" ++
  "  li t0, 56; bgeu a1, t0, .Lrbes_long\n" ++
  "  addi a0, a1, 1; ret\n" ++
  ".Lrbes_single_raw:\n" ++
  "  li a0, 1; ret\n" ++
  ".Lrbes_long:\n" ++
  "  mv t0, a1; li t1, 0\n" ++
  ".Lrbes_len_loop:\n" ++
  "  beqz t0, .Lrbes_len_done\n" ++
  "  srli t0, t0, 8; addi t1, t1, 1; j .Lrbes_len_loop\n" ++
  ".Lrbes_len_done:\n" ++
  "  add a0, a1, t1; addi a0, a0, 1; ret"

def rlpListEncodedSizeFunction : String :=
  "rlp_list_encoded_size:\n" ++
  "  li t0, 56; bgeu a0, t0, .Lrles_long\n" ++
  "  addi a0, a0, 1; ret\n" ++
  ".Lrles_long:\n" ++
  "  mv t0, a0; li t1, 0\n" ++
  ".Lrles_len_loop:\n" ++
  "  beqz t0, .Lrles_len_done\n" ++
  "  srli t0, t0, 8; addi t1, t1, 1; j .Lrles_len_loop\n" ++
  ".Lrles_len_done:\n" ++
  "  add a0, a0, t1; addi a0, a0, 1; ret"

def blockRlpRebuiltSizeFunction : String :=
  "block_rlp_rebuilt_size:\n" ++
  "  addi sp, sp, -96\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  sd s8, 72(sp); sd s9, 80(sp); sd s10, 88(sp)\n" ++
  "  mv s0, a0                   # payload\n" ++
  "  mv s1, a1                   # header RLP length\n" ++
  "  mv s2, a2                   # SSZ_BASE (reserved for future schema checks)\n" ++
  "  addi a0, s0, 504; jal ra, bgv_u32le; mv s3, a0    # tx_off\n" ++
  "  addi a0, s0, 508; jal ra, bgv_u32le; mv s4, a0    # withdrawals_off\n" ++
  "  bltu s4, s3, .Lbrl_fail\n" ++
  "  addi a0, s0, 528; jal ra, bgv_u32le; mv s5, a0    # block_access_list_off\n" ++
  "  bltu s5, s4, .Lbrl_fail\n" ++
  "  add s6, s0, s3              # tx section ptr\n" ++
  "  sub s7, s4, s3              # tx section len\n" ++
  "  li s8, 0                    # tx list payload length\n" ++
  "  beqz s7, .Lbrl_tx_list_size\n" ++
  "  mv a0, s6; jal ra, bgv_u32le; mv s9, a0           # first SSZ offset = 4*N\n" ++
  "  li t0, 4; remu t1, s9, t0; bnez t1, .Lbrl_fail\n" ++
  "  bltu s7, s9, .Lbrl_fail\n" ++
  "  divu s10, s9, t0            # tx count\n" ++
  "  li s2, 0                    # i\n" ++
  ".Lbrl_tx_loop:\n" ++
  "  bgeu s2, s10, .Lbrl_tx_list_size\n" ++
  "  slli t3, s2, 2; add a0, s6, t3; jal ra, bgv_u32le; la t0, brl_item_start; sd a0, 0(t0)\n" ++
  "  addi t5, s2, 1; bgeu t5, s10, .Lbrl_tx_last\n" ++
  "  slli t6, t5, 2; add a0, s6, t6; jal ra, bgv_u32le; la t0, brl_item_end; sd a0, 0(t0); j .Lbrl_tx_have_end\n" ++
  ".Lbrl_tx_last:\n" ++
  "  la t0, brl_item_end; sd s7, 0(t0)\n" ++
  ".Lbrl_tx_have_end:\n" ++
  "  la t0, brl_item_start; ld t4, 0(t0); la t0, brl_item_end; ld t5, 0(t0)\n" ++
  "  bltu t4, s9, .Lbrl_fail\n" ++
  "  bltu t5, t4, .Lbrl_fail\n" ++
  "  bltu s7, t5, .Lbrl_fail\n" ++
  "  add t6, s6, t4; sub a1, t5, t4\n" ++
  "  beqz a1, .Lbrl_tx_as_bytes\n" ++
  "  lbu t0, 0(t6); li t1, 0xc0; bgeu t0, t1, .Lbrl_tx_as_legacy\n" ++
  ".Lbrl_tx_as_bytes:\n" ++
  "  mv a0, t6; jal ra, rlp_bytes_encoded_size\n" ++
  "  add s8, s8, a0; j .Lbrl_tx_next\n" ++
  ".Lbrl_tx_as_legacy:\n" ++
  "  add s8, s8, a1\n" ++
  ".Lbrl_tx_next:\n" ++
  "  addi s2, s2, 1; j .Lbrl_tx_loop\n" ++
  ".Lbrl_tx_list_size:\n" ++
  "  mv a0, s8; jal ra, rlp_list_encoded_size; mv s8, a0\n" ++
  "  add s6, s0, s4              # withdrawals section ptr\n" ++
  "  sub s7, s5, s4              # withdrawals section len\n" ++
  "  li t0, 44; remu t1, s7, t0; bnez t1, .Lbrl_fail\n" ++
  "  divu s9, s7, t0             # withdrawal count\n" ++
  "  li s10, 0                   # withdrawal list payload length\n" ++
  "  li s2, 0\n" ++
  ".Lbrl_wd_loop:\n" ++
  "  bgeu s2, s9, .Lbrl_wd_list_size\n" ++
  "  li t0, 44; mul t1, s2, t0; add a0, s6, t1\n" ++
  "  la a1, brl_wd_buf; la a2, brl_wd_len; jal ra, ssz_withdrawal_to_rlp\n" ++
  "  bnez a0, .Lbrl_fail\n" ++
  "  la t0, brl_wd_len; ld t1, 0(t0); add s10, s10, t1\n" ++
  "  addi s2, s2, 1; j .Lbrl_wd_loop\n" ++
  ".Lbrl_wd_list_size:\n" ++
  "  mv a0, s10; jal ra, rlp_list_encoded_size; mv s10, a0\n" ++
  "  add t0, s1, s8              # header + txs\n" ++
  "  addi t0, t0, 1              # empty ommers list = 0xc0\n" ++
  "  add t0, t0, s10             # + withdrawals\n" ++
  "  mv a0, t0; jal ra, rlp_list_encoded_size\n" ++
  "  mv a1, a0; li a0, 0; j .Lbrl_ret\n" ++
  ".Lbrl_fail:\n" ++
  "  li a0, 1; li a1, 0\n" ++
  ".Lbrl_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp); ld s9, 80(sp); ld s10, 88(sp)\n" ++
  "  addi sp, sp, 96\n" ++
  "  ret"

end EvmAsm.Codegen
