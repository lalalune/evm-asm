/-
  EvmAsm.Codegen.Programs.TxGasSenderBalLookup

  Sender BAL pre-state lookup for transaction upfront gas checks.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.Account
import EvmAsm.Codegen.Programs.Address
import EvmAsm.Codegen.Programs.BalAccountPostFields
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.Tx

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## tx_gas_sender_bal_lookup

    Locate the BAL row and pre-state account fields for a selected tx sender.

    Calling convention:
      a0 = tx ptr
      a1 = tx len
      a2 = selected sender public key ptr (64 B x||y)
      a3 = BAL AccountChanges list ptr
      a4 = BAL AccountChanges list len
      a5 = pre-account record array ptr, 24 B per BAL row:
           +0 account_rlp_ptr, +8 account_rlp_len, +16 flags
      a6 = output ptr

    Output:
      +0   status
             0 ok
             1 malformed tx/envelope
             2 malformed BAL row/list
             3 sender BAL row not found
             4 pre-account parse failed
             5 post-field parse failed
      +8   BAL row index, or UINT64_MAX on failure before match
      +16  sender address (20 B, then zero padding)
      +48  pre balance, u256 BE
      +80  pre nonce, u64 LE
      +88  post balance byte length, UINT64_MAX when absent
      +96  post balance bytes, capacity 32
      +128 post nonce byte length, UINT64_MAX when absent
      +136 post nonce bytes, capacity 32
-/
def txGasSenderBalLookupFunction : String :=
  "tx_gas_sender_bal_lookup:\n" ++
  "  addi sp, sp, -112\n" ++
  "  sd ra,   0(sp)\n" ++
  "  sd s0,   8(sp); sd s1,  16(sp); sd s2,  24(sp); sd s3,  32(sp)\n" ++
  "  sd s4,  40(sp); sd s5,  48(sp); sd s6,  56(sp); sd s7,  64(sp)\n" ++
  "  sd s8,  72(sp); sd s9,  80(sp); sd s10, 88(sp); sd s11, 96(sp)\n" ++
  "  mv s0, a0                   # tx ptr\n" ++
  "  mv s1, a1                   # tx len\n" ++
  "  mv s2, a2                   # pubkey ptr\n" ++
  "  mv s3, a3                   # BAL ptr\n" ++
  "  mv s4, a4                   # BAL len\n" ++
  "  mv s5, a5                   # pre-account records ptr\n" ++
  "  mv s6, a6                   # output ptr\n" ++
  "  # Clear fixed output area and install absent sentinels.\n" ++
  "  sd zero,   0(s6); sd zero,  16(s6); sd zero,  24(s6); sd zero,  32(s6)\n" ++
  "  sd zero,  40(s6); sd zero,  48(s6); sd zero,  56(s6); sd zero,  64(s6)\n" ++
  "  sd zero,  72(s6); sd zero,  80(s6); sd zero,  96(s6); sd zero, 104(s6)\n" ++
  "  sd zero, 112(s6); sd zero, 136(s6); sd zero, 144(s6); sd zero, 152(s6)\n" ++
  "  sd zero, 160(s6)\n" ++
  "  li t0, -1; sd t0, 8(s6); sd t0, 88(s6); sd t0, 128(s6)\n" ++
  "  # Validate tx envelope shape. Sender recovery itself is provided by the\n" ++
  "  # selected EEST public key, matching existing BAL sender-scan helpers.\n" ++
  "  beqz s1, .Ltgsbl_bad_tx\n" ++
  "  lbu t0, 0(s0)\n" ++
  "  li t1, 0x80\n" ++
  "  bltu t0, t1, .Ltgsbl_typed_tx\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 0; la a3, tgsbl_tmp_off; la a4, tgsbl_tmp_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Ltgsbl_bad_tx\n" ++
  "  j .Ltgsbl_have_tx\n" ++
  ".Ltgsbl_typed_tx:\n" ++
  "  beqz t0, .Ltgsbl_bad_tx\n" ++
  "  li t1, 4; bgtu t0, t1, .Ltgsbl_bad_tx\n" ++
  "  li t1, 2; bltu s1, t1, .Ltgsbl_bad_tx\n" ++
  "  addi a0, s0, 1; addi a1, s1, -1; li a2, 0; la a3, tgsbl_tmp_off; la a4, tgsbl_tmp_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Ltgsbl_bad_tx\n" ++
  ".Ltgsbl_have_tx:\n" ++
  "  mv a0, s2; addi a1, s6, 16\n" ++
  "  jal ra, address_from_pubkey\n" ++
  "  mv a0, s3; mv a1, s4; la a2, tgsbl_count\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Ltgsbl_bad_bal\n" ++
  "  la t0, tgsbl_count; ld s8, 0(t0)\n" ++
  "  li s9, 0                    # row index\n" ++
  ".Ltgsbl_loop:\n" ++
  "  bgeu s9, s8, .Ltgsbl_missing\n" ++
  "  mv a0, s3; mv a1, s4; mv a2, s9; la a3, tgsbl_row_off; la a4, tgsbl_row_len\n" ++
  "  jal ra, rlp_item_span\n" ++
  "  bnez a0, .Ltgsbl_bad_bal\n" ++
  "  la t0, tgsbl_row_off; ld t0, 0(t0); add s10, s3, t0\n" ++
  "  la t0, tgsbl_row_len; ld s11, 0(t0)\n" ++
  "  mv a0, s10; mv a1, s11; li a2, 0; la a3, tgsbl_addr_off; la a4, tgsbl_addr_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Ltgsbl_bad_bal\n" ++
  "  la t0, tgsbl_addr_len; ld t0, 0(t0); li t1, 20; bne t0, t1, .Ltgsbl_bad_bal\n" ++
  "  la t0, tgsbl_addr_off; ld t0, 0(t0); add t0, s10, t0\n" ++
  "  addi t1, s6, 16\n" ++
  "  li t2, 20\n" ++
  ".Ltgsbl_cmp:\n" ++
  "  beqz t2, .Ltgsbl_match\n" ++
  "  lbu t3, 0(t0); lbu t4, 0(t1); bne t3, t4, .Ltgsbl_next\n" ++
  "  addi t0, t0, 1; addi t1, t1, 1; addi t2, t2, -1\n" ++
  "  j .Ltgsbl_cmp\n" ++
  ".Ltgsbl_next:\n" ++
  "  addi s9, s9, 1\n" ++
  "  j .Ltgsbl_loop\n" ++
  ".Ltgsbl_match:\n" ++
  "  sd s9, 8(s6)\n" ++
  "  slli t0, s9, 4; slli t1, s9, 3; add t0, t0, t1; add t0, s5, t0\n" ++
  "  ld a0, 0(t0); ld a1, 8(t0); addi a2, s6, 48\n" ++
  "  jal ra, account_extract_balance\n" ++
  "  bnez a0, .Ltgsbl_bad_account\n" ++
  "  slli t0, s9, 4; slli t1, s9, 3; add t0, t0, t1; add t0, s5, t0\n" ++
  "  ld a0, 0(t0); ld a1, 8(t0); addi a2, s6, 80\n" ++
  "  jal ra, account_extract_nonce\n" ++
  "  bnez a0, .Ltgsbl_bad_account\n" ++
  "  mv a0, s10; mv a1, s11; addi a2, s6, 96; addi a3, s6, 88; addi a4, s6, 136; addi a5, s6, 128\n" ++
  "  jal ra, bal_account_post_fields\n" ++
  "  bnez a0, .Ltgsbl_bad_post\n" ++
  "  li a0, 0\n" ++
  "  j .Ltgsbl_store_status\n" ++
  ".Ltgsbl_bad_tx:\n" ++
  "  li a0, 1; j .Ltgsbl_store_status\n" ++
  ".Ltgsbl_bad_bal:\n" ++
  "  li a0, 2; j .Ltgsbl_store_status\n" ++
  ".Ltgsbl_missing:\n" ++
  "  li a0, 3; j .Ltgsbl_store_status\n" ++
  ".Ltgsbl_bad_account:\n" ++
  "  li a0, 4; j .Ltgsbl_store_status\n" ++
  ".Ltgsbl_bad_post:\n" ++
  "  li a0, 5\n" ++
  ".Ltgsbl_store_status:\n" ++
  "  sd a0, 0(s6)\n" ++
  "  ld ra,   0(sp)\n" ++
  "  ld s0,   8(sp); ld s1,  16(sp); ld s2,  24(sp); ld s3,  32(sp)\n" ++
  "  ld s4,  40(sp); ld s5,  48(sp); ld s6,  56(sp); ld s7,  64(sp)\n" ++
  "  ld s8,  72(sp); ld s9,  80(sp); ld s10, 88(sp); ld s11, 96(sp)\n" ++
  "  addi sp, sp, 112\n" ++
  "  ret"

/-- Probe input:
      +8  tx_len
      +16 BAL len
      +24 account count
      +32 pubkey64
      +96 tx bytes
      align8, BAL bytes
      align8, account length table (u64 each), account RLP blobs align8 each.
-/
def ziskTxGasSenderBalLookupPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li s0, 0x40000000\n" ++
  "  ld s1, 8(s0)                # tx_len\n" ++
  "  ld s2, 16(s0)               # BAL len\n" ++
  "  ld s3, 24(s0)               # account count\n" ++
  "  addi s4, s0, 32             # pubkey ptr\n" ++
  "  addi s5, s0, 96             # tx ptr\n" ++
  "  add t0, s5, s1; addi t0, t0, 7; li t1, -8; and s6, t0, t1 # BAL ptr\n" ++
  "  add t0, s6, s2; addi t0, t0, 7; li t1, -8; and s7, t0, t1 # length table\n" ++
  "  slli t0, s3, 3; add s8, s7, t0   # account blob cursor\n" ++
  "  la s9, tgsbl_records\n" ++
  "  li s10, 0\n" ++
  ".Ltgsblp_records:\n" ++
  "  bgeu s10, s3, .Ltgsblp_call\n" ++
  "  slli t0, s10, 3; add t1, s7, t0; ld t2, 0(t1) # account len\n" ++
  "  slli t3, s10, 4; add t4, t3, t0; add t4, s9, t4\n" ++
  "  sd s8, 0(t4); sd t2, 8(t4); sd zero, 16(t4)\n" ++
  "  add s8, s8, t2; addi s8, s8, 7; li t5, -8; and s8, s8, t5\n" ++
  "  addi s10, s10, 1\n" ++
  "  j .Ltgsblp_records\n" ++
  ".Ltgsblp_call:\n" ++
  "  mv a0, s5; mv a1, s1; mv a2, s4; mv a3, s6; mv a4, s2; mv a5, s9\n" ++
  "  li a6, 0xa0010000\n" ++
  "  jal ra, tx_gas_sender_bal_lookup\n" ++
  "  j .Ltgsblp_done\n" ++
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
  ".Ltgsblp_done:"

def ziskTxGasSenderBalLookupDataSection : String :=
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
  ".balign 32\n" ++
  "afp_digest:\n  .zero 32\n" ++
  "zk3_state:\n  .zero 200\n" ++
  ".balign 8\n" ++
  "tgsbl_records:\n  .zero 4096"

def ziskTxGasSenderBalLookupProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskTxGasSenderBalLookupPrologue
  dataAsm     := ziskTxGasSenderBalLookupDataSection
}

end EvmAsm.Codegen
