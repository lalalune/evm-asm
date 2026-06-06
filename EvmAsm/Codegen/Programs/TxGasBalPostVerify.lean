/-
  EvmAsm.Codegen.Programs.TxGasBalPostVerify

  BAL-facing pre-execution gas verifier for one transaction sender.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.Account
import EvmAsm.Codegen.Programs.Address
import EvmAsm.Codegen.Programs.BalAccountPostFields
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.TxGasSenderBalLookup
import EvmAsm.Codegen.Programs.U256GasPricing

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## tx_gas_bal_post_verify

    Compose sender BAL lookup with the transaction upfront gas precharge helper.
    This first BAL-facing slice validates the sender nonce post-field against
    the nonce after pre-execution charge. It deliberately reports the charged
    balance as a diagnostic but does not require exact final balance yet, because
    post-execution refunds and settlement are wired by later gas beads.

    Calling convention:
      a0 = tx ptr
      a1 = tx len
      a2 = base_fee_per_gas ptr (32 B BE)
      a3 = selected sender public key ptr (64 B x||y)
      a4 = BAL AccountChanges list ptr
      a5 = BAL AccountChanges list len
      a6 = pre-account record array ptr
      a7 = output ptr

    Output:
      +0   status
             0  ok
             10 sender BAL lookup failed
             20 tx upfront precharge failed
             30 sender BAL post nonce absent
             31 sender BAL post nonce exceeds u64
             32 sender BAL post nonce mismatch
      +8   lookup status
      +16  precharge status
      +24  BAL row index, or UINT64_MAX
      +32  pre nonce
      +40  charged nonce
      +48  post nonce len
      +56  post nonce u64
      +64  post balance len
      +72  charged balance, u256 BE
      +104 sender address, 20 B
-/
def txGasBalPostVerifyFunction : String :=
  "tx_gas_bal_post_verify:\n" ++
  "  addi sp, sp, -112\n" ++
  "  sd ra,   0(sp)\n" ++
  "  sd s0,   8(sp); sd s1,  16(sp); sd s2,  24(sp); sd s3,  32(sp)\n" ++
  "  sd s4,  40(sp); sd s5,  48(sp); sd s6,  56(sp); sd s7,  64(sp)\n" ++
  "  sd s8,  72(sp); sd s9,  80(sp); sd s10, 88(sp); sd s11, 96(sp)\n" ++
  "  mv s0, a0                   # tx ptr\n" ++
  "  mv s1, a1                   # tx len\n" ++
  "  mv s2, a2                   # base fee ptr\n" ++
  "  mv s3, a3                   # pubkey ptr\n" ++
  "  mv s4, a4                   # BAL ptr\n" ++
  "  mv s5, a5                   # BAL len\n" ++
  "  mv s6, a6                   # pre-account records ptr\n" ++
  "  mv s7, a7                   # output ptr\n" ++
  "  # Clear output and install absent sentinels.\n" ++
  "  sd zero,   0(s7); sd zero,   8(s7); sd zero,  16(s7); sd zero,  24(s7)\n" ++
  "  sd zero,  32(s7); sd zero,  40(s7); sd zero,  48(s7); sd zero,  56(s7)\n" ++
  "  sd zero,  64(s7); sd zero,  72(s7); sd zero,  80(s7); sd zero,  88(s7)\n" ++
  "  sd zero,  96(s7); sd zero, 104(s7); sd zero, 112(s7); sd zero, 120(s7)\n" ++
  "  li t0, -1; sd t0, 24(s7); sd t0, 48(s7); sd t0, 64(s7)\n" ++
  "  # Locate sender BAL row and pre/post scalar fields.\n" ++
  "  mv a0, s0; mv a1, s1; mv a2, s3; mv a3, s4; mv a4, s5; mv a5, s6\n" ++
  "  la a6, tgbpv_lookup\n" ++
  "  jal ra, tx_gas_sender_bal_lookup\n" ++
  "  la t0, tgbpv_lookup; ld t1, 0(t0); sd t1, 8(s7)\n" ++
  "  ld t2, 8(t0); sd t2, 24(s7)\n" ++
  "  ld t2, 80(t0); sd t2, 32(s7)\n" ++
  "  ld t2, 128(t0); sd t2, 48(s7)\n" ++
  "  ld t2, 88(t0); sd t2, 64(s7)\n" ++
  "  addi t3, t0, 16; addi t4, s7, 104; li t5, 20\n" ++
  ".Ltgbpv_copy_addr:\n" ++
  "  beqz t5, .Ltgbpv_after_addr\n" ++
  "  lbu t6, 0(t3); sb t6, 0(t4)\n" ++
  "  addi t3, t3, 1; addi t4, t4, 1; addi t5, t5, -1\n" ++
  "  j .Ltgbpv_copy_addr\n" ++
  ".Ltgbpv_after_addr:\n" ++
  "  beqz t1, .Ltgbpv_have_lookup\n" ++
  "  li t0, 10; sd t0, 0(s7)\n" ++
  "  j .Ltgbpv_ret\n" ++
  ".Ltgbpv_have_lookup:\n" ++
  "  # Copy mutable pre-balance and pre-nonce into local scratch.\n" ++
  "  la t0, tgbpv_lookup; addi t1, t0, 48; la t2, tgbpv_balance\n" ++
  "  ld t3,  0(t1); sd t3,  0(t2)\n" ++
  "  ld t3,  8(t1); sd t3,  8(t2)\n" ++
  "  ld t3, 16(t1); sd t3, 16(t2)\n" ++
  "  ld t3, 24(t1); sd t3, 24(t2)\n" ++
  "  ld t3, 80(t0); la t4, tgbpv_nonce; sd t3, 0(t4)\n" ++
  "  mv a0, s0; mv a1, s1; mv a2, s2; la a3, tgbpv_balance; la a4, tgbpv_nonce\n" ++
  "  jal ra, tx_upfront_precharge\n" ++
  "  sd a0, 16(s7)\n" ++
  "  la t0, tgbpv_nonce; ld t1, 0(t0); sd t1, 40(s7)\n" ++
  "  la t0, tgbpv_balance\n" ++
  "  ld t2,  0(t0); sd t2,  72(s7)\n" ++
  "  ld t2,  8(t0); sd t2,  80(s7)\n" ++
  "  ld t2, 16(t0); sd t2,  88(s7)\n" ++
  "  ld t2, 24(t0); sd t2,  96(s7)\n" ++
  "  beqz a0, .Ltgbpv_have_precharge\n" ++
  "  li t0, 20; sd t0, 0(s7)\n" ++
  "  j .Ltgbpv_ret\n" ++
  ".Ltgbpv_have_precharge:\n" ++
  "  la t0, tgbpv_lookup; ld s8, 128(t0) # post nonce len\n" ++
  "  li t1, -1; bne s8, t1, .Ltgbpv_nonce_present\n" ++
  "  li t0, 30; sd t0, 0(s7)\n" ++
  "  j .Ltgbpv_ret\n" ++
  ".Ltgbpv_nonce_present:\n" ++
  "  li t1, 8; bleu s8, t1, .Ltgbpv_nonce_len_ok\n" ++
  "  li t0, 31; sd t0, 0(s7)\n" ++
  "  j .Ltgbpv_ret\n" ++
  ".Ltgbpv_nonce_len_ok:\n" ++
  "  li s9, 0                    # raw BE nonce accumulator\n" ++
  "  la t0, tgbpv_lookup; addi s10, t0, 136\n" ++
  "  mv s11, s8\n" ++
  ".Ltgbpv_nonce_be_loop:\n" ++
  "  beqz s11, .Ltgbpv_nonce_be_done\n" ++
  "  slli s9, s9, 8\n" ++
  "  lbu t0, 0(s10); or s9, s9, t0\n" ++
  "  addi s10, s10, 1; addi s11, s11, -1\n" ++
  "  j .Ltgbpv_nonce_be_loop\n" ++
  ".Ltgbpv_nonce_be_done:\n" ++
  "  sd s9, 56(s7)\n" ++
  "  la t0, tgbpv_nonce; ld t1, 0(t0); beq s9, t1, .Ltgbpv_ok\n" ++
  "  li t0, 32; sd t0, 0(s7)\n" ++
  "  j .Ltgbpv_ret\n" ++
  ".Ltgbpv_ok:\n" ++
  "  sd zero, 0(s7)\n" ++
  ".Ltgbpv_ret:\n" ++
  "  ld ra,   0(sp)\n" ++
  "  ld s0,   8(sp); ld s1,  16(sp); ld s2,  24(sp); ld s3,  32(sp)\n" ++
  "  ld s4,  40(sp); ld s5,  48(sp); ld s6,  56(sp); ld s7,  64(sp)\n" ++
  "  ld s8,  72(sp); ld s9,  80(sp); ld s10, 88(sp); ld s11, 96(sp)\n" ++
  "  addi sp, sp, 112\n" ++
  "  ret"

/- Probe input:
      +8   tx_len
      +16  BAL len
      +24  account count
      +32  base_fee_per_gas, 32 B BE
      +64  sender pubkey, 64 B
      +128 tx bytes
      align8, BAL bytes
      align8, account length table (u64 each), account RLP blobs align8 each.
-/
def ziskTxGasBalPostVerifyPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li s0, 0x40000000\n" ++
  "  ld s1, 8(s0)                # tx_len\n" ++
  "  ld s2, 16(s0)               # BAL len\n" ++
  "  ld s3, 24(s0)               # account count\n" ++
  "  addi s4, s0, 32             # base_fee ptr\n" ++
  "  addi s5, s0, 64             # pubkey ptr\n" ++
  "  addi s6, s0, 128            # tx ptr\n" ++
  "  add t0, s6, s1; addi t0, t0, 7; li t1, -8; and s7, t0, t1 # BAL ptr\n" ++
  "  add t0, s7, s2; addi t0, t0, 7; li t1, -8; and s8, t0, t1 # length table\n" ++
  "  slli t0, s3, 3; add s9, s8, t0   # account blob cursor\n" ++
  "  la s10, tgbpv_records\n" ++
  "  li s11, 0\n" ++
  ".Ltgbpvp_records:\n" ++
  "  bgeu s11, s3, .Ltgbpvp_call\n" ++
  "  slli t0, s11, 3; add t1, s8, t0; ld t2, 0(t1) # account len\n" ++
  "  slli t3, s11, 4; add t4, t3, t0; add t4, s10, t4\n" ++
  "  sd s9, 0(t4); sd t2, 8(t4); sd zero, 16(t4)\n" ++
  "  add s9, s9, t2; addi s9, s9, 7; li t5, -8; and s9, s9, t5\n" ++
  "  addi s11, s11, 1\n" ++
  "  j .Ltgbpvp_records\n" ++
  ".Ltgbpvp_call:\n" ++
  "  mv a0, s6; mv a1, s1; mv a2, s4; mv a3, s5; mv a4, s7; mv a5, s2; mv a6, s10\n" ++
  "  li a7, 0xa0010000\n" ++
  "  jal ra, tx_gas_bal_post_verify\n" ++
  "  j .Ltgbpvp_done\n" ++
  zkvmKeccak256Function ++ "\n" ++
  addressFromPubkeyFunction ++ "\n" ++
  rlpItemSizeFunction ++ "\n" ++
  rlpItemSpanFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  rlpFieldToU256BeFunction ++ "\n" ++
  accountExtractBalanceFunction ++ "\n" ++
  accountExtractNonceFunction ++ "\n" ++
  balAccountPostFieldsFunction ++ "\n" ++
  txGasSenderBalLookupFunction ++ "\n" ++
  txTypeDispatchFunction ++ "\n" ++
  txExtractNonceAndGasFunction ++ "\n" ++
  txExtractGasPricingFunction ++ "\n" ++
  u256SubBeFunction ++ "\n" ++
  u256MinFunction ++ "\n" ++
  u256AddBeFunction ++ "\n" ++
  priorityFeePerGasEip1559Function ++ "\n" ++
  txEffectiveGasPricingFunction ++ "\n" ++
  u256MulU64BeFunction ++ "\n" ++
  accountChargeGasPreExecFunction ++ "\n" ++
  txUpfrontPrechargeFunction ++ "\n" ++
  txGasBalPostVerifyFunction ++ "\n" ++
  ".Ltgbpvp_done:"

def ziskTxGasBalPostVerifyDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "tgsbl_tmp_off:\n  .zero 8\n" ++
  "tgsbl_tmp_len:\n  .zero 8\n" ++
  "tgsbl_count:\n  .zero 8\n" ++
  "tgsbl_row_off:\n  .zero 8\n" ++
  "tgsbl_row_len:\n  .zero 8\n" ++
  "tgsbl_addr_off:\n  .zero 8\n" ++
  "tgsbl_addr_len:\n  .zero 8\n" ++
  "rfu_offset:\n  .zero 8\n" ++
  "rfu_length:\n  .zero 8\n" ++
  "bpf_list_off:\n  .zero 8\n" ++
  "bpf_list_len:\n  .zero 8\n" ++
  "bpf_list_ptr:\n  .zero 8\n" ++
  "bpf_count:\n  .zero 8\n" ++
  "bpf_item_off:\n  .zero 8\n" ++
  "bpf_item_len:\n  .zero 8\n" ++
  "bpf_item_ptr:\n  .zero 8\n" ++
  "bpf_val_off:\n  .zero 8\n" ++
  "bpf_val_len:\n  .zero 8\n" ++
  "teng_type:\n  .zero 8\n" ++
  "teng_inner_off:\n  .zero 8\n" ++
  "tegp_type:\n  .zero 8\n" ++
  "tegp_inner_off:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "afp_digest:\n  .zero 32\n" ++
  "zk3_state:\n  .zero 200\n" ++
  ".balign 32\n" ++
  "tefgp_max_priority:\n  .zero 32\n" ++
  "tefgp_max_fee:\n  .zero 32\n" ++
  "tefgp_tmp:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "txup_nonce:\n  .zero 8\n" ++
  "txup_gas_limit:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "txup_effective_gas_price:\n  .zero 32\n" ++
  "txup_priority_fee:\n  .zero 32\n" ++
  "u256m_acc:\n  .zero 40\n" ++
  ".balign 32\n" ++
  "acpg_gas_fee:\n  .zero 32\n" ++
  "tgbpv_balance:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "tgbpv_nonce:\n  .zero 8\n" ++
  "tgbpv_lookup:\n  .zero 168\n" ++
  "tgbpv_records:\n  .zero 4096"

def ziskTxGasBalPostVerifyProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskTxGasBalPostVerifyPrologue
  dataAsm     := ziskTxGasBalPostVerifyDataSection
}

end EvmAsm.Codegen
