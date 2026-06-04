/-
  EvmAsm.Codegen.Programs.BlockVerdictReceiptRecords

  Receipt-record materialization helpers carved out of BlockVerdict.lean to keep
  the main stateless verdict file below the file-size cap.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.BalGasValid
import EvmAsm.Codegen.Programs.TxExtract
import EvmAsm.Codegen.Programs.ReceiptRecords

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## block_receipt_records_materialize -- first receipt-record integration.
    a0 = execution payload ptr.

    This deliberately handles only the smallest useful materialization surface
    before full transaction execution exists: zero transactions leaves the arena
    empty, and one legacy transaction in an otherwise successful block appends a
    success record with cumulative_gas_used = payload.gas_used and no logs. Other
    transaction shapes leave a debug status but do not affect the block verdict. -/
def blockReceiptRecordsMaterializeFunction : String :=
  "block_receipt_records_materialize:\n" ++
  "  addi sp, sp, -80\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  mv s0, a0                   # execution payload\n" ++
  "  la t0, brr_status; sd zero, 0(t0)\n" ++
  "  la t0, brr_append_status; sd zero, 0(t0)\n" ++
  "  la a0, brr_control; li a1, 16; la a2, brr_records\n" ++
  "  jal ra, receipt_records_init\n" ++
  "  addi a0, s0, 504; jal ra, bgv_u32le\n" ++
  "  mv s1, a0                   # transactions_offset\n" ++
  "  addi a0, s0, 508; jal ra, bgv_u32le\n" ++
  "  mv s2, a0                   # withdrawals_offset\n" ++
  "  bleu s2, s1, .Lbrr_ok       # zero transactions\n" ++
  "  add s3, s0, s1              # tx list ptr\n" ++
  "  sub s4, s2, s1              # tx list len\n" ++
  "  li t0, 4; bltu s4, t0, .Lbrr_unsupported\n" ++
  "  mv a0, s3; jal ra, bgv_u32le\n" ++
  "  andi t0, a0, 3; bnez t0, .Lbrr_unsupported\n" ++
  "  srli s5, a0, 2              # tx_count\n" ++
  "  beqz s5, .Lbrr_ok\n" ++
  "  li t0, 1; bne s5, t0, .Lbrr_unsupported\n" ++
  "  bgtu a0, s4, .Lbrr_unsupported\n" ++
  "  mv s6, a0                   # first tx offset\n" ++
  "  sub s7, s4, s6              # tx len\n" ++
  "  add s6, s3, s6              # tx ptr\n" ++
  "  mv a0, s6; mv a1, s7; la a2, brr_tx_type; la a3, brr_tx_inner\n" ++
  "  jal ra, tx_type_dispatch\n" ++
  "  bnez a0, .Lbrr_unsupported\n" ++
  "  la t0, brr_tx_type; ld t1, 0(t0); bnez t1, .Lbrr_unsupported\n" ++
  "  addi a0, s0, 420; jal ra, bgv_u64le        # payload.gas_used\n" ++
  "  mv a3, a0                                  # cumulative gas\n" ++
  "  la a0, brr_control\n" ++
  "  li a1, 0                    # legacy tx type\n" ++
  "  li a2, 1                    # successful execution\n" ++
  "  li a4, 0                    # pre-tx event log checkpoint\n" ++
  "  li a5, 0                    # final event log count\n" ++
  "  jal ra, receipt_records_append_runtime_result\n" ++
  "  la t0, brr_append_status; sd a0, 0(t0)\n" ++
  "  bnez a0, .Lbrr_append_fail\n" ++
  "  j .Lbrr_ok\n" ++
  ".Lbrr_unsupported:\n" ++
  "  li t0, 1; la t1, brr_status; sd t0, 0(t1); j .Lbrr_ret\n" ++
  ".Lbrr_append_fail:\n" ++
  "  li t0, 2; la t1, brr_status; sd t0, 0(t1); j .Lbrr_ret\n" ++
  ".Lbrr_ok:\n" ++
  "  li a0, 0; j .Lbrr_ret\n" ++
  ".Lbrr_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  addi sp, sp, 80\n" ++
  "  ret"

/-- `zisk_block_receipt_records_materialize`: focused probe for the first
    block-verdict receipt-record materialization slice. The input is a synthetic
    execution-payload byte array at INPUT_ADDR with only the fields this helper
    reads populated: gas_used, transactions_offset, withdrawals_offset, and the
    transactions SSZ list bytes. Output layout:
      +0  brr_status
      +8  receipt count
      +16 append status
      +24 first-record nth status
      +32 first 64-byte record copy, zero if absent. -/
def ziskBlockReceiptRecordsMaterializePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t0, 0xa0010000\n" ++
  "  li t1, 24\n" ++
  ".Lbrrp_zero_out:\n" ++
  "  beqz t1, .Lbrrp_zero_done\n" ++
  "  sd zero, 0(t0)\n" ++
  "  addi t0, t0, 8\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Lbrrp_zero_out\n" ++
  ".Lbrrp_zero_done:\n" ++
  "  li a0, 0x40000008\n" ++
  "  jal ra, block_receipt_records_materialize\n" ++
  "  li s0, 0xa0010000\n" ++
  "  la t1, brr_status; ld t2, 0(t1); sd t2, 0(s0)\n" ++
  "  la t1, brr_control; ld t2, 0(t1); sd t2, 8(s0)\n" ++
  "  la t1, brr_append_status; ld t2, 0(t1); sd t2, 16(s0)\n" ++
  "  la a0, brr_control; li a1, 0; addi a2, s0, 32\n" ++
  "  jal ra, receipt_record_nth\n" ++
  "  sd a0, 24(s0)\n" ++
  "  j .Lbrrp_done\n" ++
  bgvU32leFunction ++ "\n" ++
  bgvU64leFunction ++ "\n" ++
  txTypeDispatchFunction ++ "\n" ++
  receiptRecordsFunction ++ "\n" ++
  blockReceiptRecordsMaterializeFunction ++ "\n" ++
  ".Lbrrp_done:"

def ziskBlockReceiptRecordsMaterializeDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "brr_status:\n  .zero 8\n" ++
  "brr_append_status:\n  .zero 8\n" ++
  "brr_tx_type:\n  .zero 8\n" ++
  "brr_tx_inner:\n  .zero 8\n" ++
  "brr_control:\n  .zero 24\n" ++
  ".balign 8\n" ++
  "brr_records:\n  .zero 1024"

def ziskBlockReceiptRecordsMaterializeProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBlockReceiptRecordsMaterializePrologue
  dataAsm     := ziskBlockReceiptRecordsMaterializeDataSection
}

end EvmAsm.Codegen
