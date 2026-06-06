/-
  EvmAsm.Codegen.Programs.BlockVerdictGasResults

  Transaction gas-result helpers for the stateless block verdict path.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.BalGasValid
import EvmAsm.Codegen.Programs.TxExtract

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## block_verdict_tx_gas_limits

    Materialize `tx.gas` values from `exec_payload.transactions`.

    ABI:
      a0 = execution payload ptr
      a1 = output pointer for `max_count` u64 gas limits
      a2 = max_count

    Returns:
      a0 = status:
        0 ok
        1 malformed SSZ transaction list offsets
        2 transaction count exceeds max_count
        3 transaction type dispatch failed
        4 nonce/gas extraction failed
      a1 = transaction count decoded from the SSZ list
      a2 = failing transaction index, 1-based; 0 if not transaction-specific
      a3 = transaction type from `tx_type_dispatch` when available

    Debug globals mirror the return values for `zisk_stateless_verdict_v2`
    wiring in the next slice. -/
def blockVerdictTxGasLimitsFunction : String :=
  "block_verdict_tx_gas_limits:\n" ++
  "  addi sp, sp, -112\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  sd s8, 72(sp); sd s9, 80(sp); sd s10, 88(sp); sd s11, 96(sp)\n" ++
  "  mv s0, a0                   # execution payload\n" ++
  "  mv s1, a1                   # gas limit output array\n" ++
  "  mv s2, a2                   # max_count\n" ++
  "  la t0, bvgr_status; sd zero, 0(t0)\n" ++
  "  la t0, bvgr_count; sd zero, 0(t0)\n" ++
  "  la t0, bvgr_fail_index; sd zero, 0(t0)\n" ++
  "  la t0, bvgr_tx_type; sd zero, 0(t0)\n" ++
  "  addi a0, s0, 504; jal ra, bgv_u32le\n" ++
  "  mv s3, a0                   # transactions_offset\n" ++
  "  addi a0, s0, 508; jal ra, bgv_u32le\n" ++
  "  mv s4, a0                   # withdrawals_offset\n" ++
  "  bleu s4, s3, .Lbvgr_ok_zero # no transactions\n" ++
  "  add s5, s0, s3              # tx list ptr\n" ++
  "  sub s6, s4, s3              # tx list byte length\n" ++
  "  li t0, 4; bltu s6, t0, .Lbvgr_malformed\n" ++
  "  mv a0, s5; jal ra, bgv_u32le\n" ++
  "  andi t0, a0, 3; bnez t0, .Lbvgr_malformed\n" ++
  "  bgtu a0, s6, .Lbvgr_malformed\n" ++
  "  srli s7, a0, 2              # tx_count\n" ++
  "  la t0, bvgr_count; sd s7, 0(t0)\n" ++
  "  bgtu s7, s2, .Lbvgr_capacity\n" ++
  "  beqz s7, .Lbvgr_ok\n" ++
  "  mv s8, zero                 # tx index\n" ++
  "  slli s11, s7, 2             # minimum item offset = offset table len\n" ++
  ".Lbvgr_loop:\n" ++
  "  beq s8, s7, .Lbvgr_ok\n" ++
  "  slli t0, s8, 2\n" ++
  "  add a0, s5, t0\n" ++
  "  jal ra, bgv_u32le\n" ++
  "  mv s9, a0                   # current tx offset\n" ++
  "  bltu s9, s11, .Lbvgr_malformed_tx\n" ++
  "  bgtu s9, s6, .Lbvgr_malformed_tx\n" ++
  "  addi t0, s8, 1\n" ++
  "  beq t0, s7, .Lbvgr_last_tx\n" ++
  "  slli t1, t0, 2\n" ++
  "  add a0, s5, t1\n" ++
  "  jal ra, bgv_u32le\n" ++
  "  mv s10, a0                  # next tx offset\n" ++
  "  j .Lbvgr_have_next\n" ++
  ".Lbvgr_last_tx:\n" ++
  "  mv s10, s6                  # final tx ends at list end\n" ++
  ".Lbvgr_have_next:\n" ++
  "  bltu s10, s9, .Lbvgr_malformed_tx\n" ++
  "  bgtu s10, s6, .Lbvgr_malformed_tx\n" ++
  "  add t0, s5, s9              # tx ptr\n" ++
  "  sub t1, s10, s9             # tx len\n" ++
  "  mv a0, t0; mv a1, t1; la a2, bvgr_tx_type; la a3, bvgr_tx_inner\n" ++
  "  jal ra, tx_type_dispatch\n" ++
  "  bnez a0, .Lbvgr_type_fail\n" ++
  "  add t0, s5, s9\n" ++
  "  sub t1, s10, s9\n" ++
  "  mv a0, t0; mv a1, t1; la a2, bvgr_nonce; la a3, bvgr_gas\n" ++
  "  jal ra, tx_extract_nonce_and_gas\n" ++
  "  bnez a0, .Lbvgr_extract_fail\n" ++
  "  slli t0, s8, 3\n" ++
  "  add t1, s1, t0\n" ++
  "  la t2, bvgr_gas; ld t3, 0(t2)\n" ++
  "  sd t3, 0(t1)\n" ++
  "  addi s8, s8, 1\n" ++
  "  j .Lbvgr_loop\n" ++
  ".Lbvgr_ok_zero:\n" ++
  "  mv s7, zero\n" ++
  ".Lbvgr_ok:\n" ++
  "  li a0, 0; mv a1, s7; li a2, 0; la t0, bvgr_tx_type; ld a3, 0(t0)\n" ++
  "  j .Lbvgr_store_ret\n" ++
  ".Lbvgr_malformed_tx:\n" ++
  "  addi a2, s8, 1; li a0, 1; mv a1, s7; j .Lbvgr_store_ret\n" ++
  ".Lbvgr_malformed:\n" ++
  "  li a0, 1; li a1, 0; li a2, 0; li a3, 0; j .Lbvgr_store_ret\n" ++
  ".Lbvgr_capacity:\n" ++
  "  li a0, 2; mv a1, s7; li a2, 0; li a3, 0; j .Lbvgr_store_ret\n" ++
  ".Lbvgr_type_fail:\n" ++
  "  li a0, 3; mv a1, s7; addi a2, s8, 1; la t0, bvgr_tx_type; ld a3, 0(t0)\n" ++
  "  j .Lbvgr_store_ret\n" ++
  ".Lbvgr_extract_fail:\n" ++
  "  li a0, 4; mv a1, s7; addi a2, s8, 1; la t0, bvgr_tx_type; ld a3, 0(t0)\n" ++
  ".Lbvgr_store_ret:\n" ++
  "  la t0, bvgr_status; sd a0, 0(t0)\n" ++
  "  la t0, bvgr_count; sd a1, 0(t0)\n" ++
  "  la t0, bvgr_fail_index; sd a2, 0(t0)\n" ++
  "  la t0, bvgr_tx_type; sd a3, 0(t0)\n" ++
  ".Lbvgr_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp); ld s9, 80(sp); ld s10, 88(sp); ld s11, 96(sp)\n" ++
  "  addi sp, sp, 112\n" ++
  "  ret"

/-- `zisk_block_verdict_tx_gas_limits`: focused probe for materializing
    transaction gas limits from an execution payload.

    Input: an execution payload byte array at `INPUT_ADDR + 8`. Output:
      +0  status
      +8  count
      +16 fail index
      +24 last/failed tx type
      +32 first gas limit
      +40 second gas limit -/
def ziskBlockVerdictTxGasLimitsPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a0, 0x40000008\n" ++
  "  la a1, bvgr_tx_gas_limits\n" ++
  "  li a2, 16\n" ++
  "  jal ra, block_verdict_tx_gas_limits\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0); sd a1, 8(t0); sd a2, 16(t0); sd a3, 24(t0)\n" ++
  "  la t1, bvgr_tx_gas_limits; ld t2, 0(t1); sd t2, 32(t0); ld t2, 8(t1); sd t2, 40(t0)\n" ++
  "  j .Lbvgr_probe_done\n" ++
  bgvU32leFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  txTypeDispatchFunction ++ "\n" ++
  txExtractNonceAndGasFunction ++ "\n" ++
  blockVerdictTxGasLimitsFunction ++ "\n" ++
  ".Lbvgr_probe_done:"

def ziskBlockVerdictTxGasLimitsDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "rfu_offset:\n  .zero 8\n" ++
  "rfu_length:\n  .zero 8\n" ++
  "teng_type:\n  .zero 8\n" ++
  "teng_inner_off:\n  .zero 8\n" ++
  "bvgr_status:\n  .zero 8\n" ++
  "bvgr_count:\n  .zero 8\n" ++
  "bvgr_fail_index:\n  .zero 8\n" ++
  "bvgr_tx_type:\n  .zero 8\n" ++
  "bvgr_tx_inner:\n  .zero 8\n" ++
  "bvgr_nonce:\n  .zero 8\n" ++
  "bvgr_gas:\n  .zero 8\n" ++
  "bvgr_tx_gas_limits:\n  .zero 128\n"

def ziskBlockVerdictTxGasLimitsProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBlockVerdictTxGasLimitsPrologue
  dataAsm     := ziskBlockVerdictTxGasLimitsDataSection
}

end EvmAsm.Codegen
