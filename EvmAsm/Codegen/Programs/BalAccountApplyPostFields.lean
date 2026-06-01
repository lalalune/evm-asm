/-
  EvmAsm.Codegen.Programs.BalAccountApplyPostFields

  Compose BAL AccountChanges post-value extraction with account RLP rewriting.

  This is the account-value half of BAL replay for post-state-root recompute:
  given the pre-state account RLP and one BAL AccountChanges item, apply the
  final nonce and/or balance post-values reported by the BAL entry. Storage and
  code changes are handled by separate trie/account-root machinery.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.AccountBalance
import EvmAsm.Codegen.Programs.AccountApplyStorage
import EvmAsm.Codegen.Programs.BalAccountPostFields

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## bal_account_apply_post_fields -- account RLP + BAL item -> post account RLP

    a0 = account RLP ptr        a1 = account RLP length
    a2 = AccountChanges ptr     a3 = AccountChanges length
    a4 = output buffer ptr      a5 = u64 out length ptr
    a0 (output) = 0 ok / 1 parse fail or value length > 32.

    A missing BAL nonce/balance change list leaves that account field unchanged.
    A zero post-value is represented by length 0 from `bal_account_post_fields`
    and is spliced as the canonical RLP integer zero. -/
def balAccountApplyPostFieldsFunction : String :=
  "bal_account_apply_post_fields:\n" ++
  "  addi sp, sp, -96\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  mv s0, a0                   # original account ptr\n" ++
  "  mv s1, a1                   # original account len\n" ++
  "  mv s2, a2                   # AccountChanges ptr\n" ++
  "  mv s3, a3                   # AccountChanges len\n" ++
  "  mv s4, a4                   # out ptr\n" ++
  "  mv s5, a5                   # out len ptr\n" ++
  "  mv s6, s0                   # current account ptr\n" ++
  "  mv s7, s1                   # current account len\n" ++
  "  mv a0, s2; mv a1, s3\n" ++
  "  la a2, baap_bal; la a3, baap_bal_len; la a4, baap_nonce; la a5, baap_nonce_len\n" ++
  "  jal ra, bal_account_post_fields\n" ++
  "  bnez a0, .Lbaap_fail\n" ++
  "  # Apply the final BAL code change first, when present. CodeChanges items are\n" ++
  "  # [blockAccessIndex, newCode]; the account field stores keccak256(newCode).\n" ++
  "  mv a0, s2; mv a1, s3; li a2, 5; la a3, baap_code_list_off; la a4, baap_code_list_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbaap_fail\n" ++
  "  la t0, baap_code_list_off; ld t0, 0(t0); add t0, s2, t0; la t1, baap_code_list_ptr; sd t0, 0(t1)\n" ++
  "  la t1, baap_code_list_len; ld a1, 0(t1); mv a0, t0; la a2, baap_code_count\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lbaap_fail\n" ++
  "  la t0, baap_code_count; ld t0, 0(t0); beqz t0, .Lbaap_storage_gate\n" ++
  "  addi a2, t0, -1; la t1, baap_code_list_ptr; ld a0, 0(t1); la t1, baap_code_list_len; ld a1, 0(t1)\n" ++
  "  la a3, baap_item_off; la a4, baap_item_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbaap_fail\n" ++
  "  la t0, baap_code_list_ptr; ld t0, 0(t0); la t1, baap_item_off; ld t1, 0(t1); add t0, t0, t1\n" ++
  "  la t1, baap_item_len; ld t1, 0(t1); la t2, baap_code_item_ptr; sd t0, 0(t2)\n" ++
  "  mv a0, t0; mv a1, t1; li a2, 1; la a3, baap_code_off; la a4, baap_code_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbaap_fail\n" ++
  "  la t0, baap_code_item_ptr; ld t0, 0(t0); la t1, baap_code_off; ld t1, 0(t1); add a0, t0, t1\n" ++
  "  la t1, baap_code_len; ld a1, 0(t1); la a2, baap_code_hash\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  la a0, baap_code_hash; li a1, 32; la a2, aab_enc; la a3, aab_enc_len\n" ++
  "  jal ra, rlp_encode_bytes\n" ++
  "  mv a0, s6; mv a1, s7; li a2, 3; la a3, aab_enc; la t0, aab_enc_len; ld a4, 0(t0)\n" ++
  "  la a5, baap_tmp3; la a6, baap_tmp3_len\n" ++
  "  jal ra, mpt_splice_slot\n" ++
  "  bnez a0, .Lbaap_fail\n" ++
  "  la s6, baap_tmp3; la t0, baap_tmp3_len; ld s7, 0(t0)\n" ++
  ".Lbaap_storage_gate:\n" ++
  "  # Apply one BAL storage change first if this account also has a nonce/balance\n" ++
  "  # post-field. Storage-only system BAL entries are handled by system writes.\n" ++
  "  la t0, baap_bal_len; ld t0, 0(t0); li t1, -1; bne t0, t1, .Lbaap_try_storage\n" ++
  "  la t0, baap_nonce_len; ld t0, 0(t0); li t1, -1; beq t0, t1, .Lbaap_nonce\n" ++
  ".Lbaap_try_storage:\n" ++
  "  mv a0, s2; mv a1, s3; li a2, 1; la a3, baap_sc_off; la a4, baap_sc_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbaap_fail\n" ++
  "  la t0, baap_sc_off; ld t0, 0(t0); add t0, s2, t0; la t1, baap_sc_ptr; sd t0, 0(t1)\n" ++
  "  la t1, baap_sc_len; ld a1, 0(t1); mv a0, t0; la a2, baap_sc_count\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lbaap_fail\n" ++
  "  la t0, baap_sc_count; ld t0, 0(t0); beqz t0, .Lbaap_nonce\n" ++
  "  li t1, 1; bne t0, t1, .Lbaap_fail\n" ++
  "  la t1, baap_sc_ptr; ld a0, 0(t1); la t1, baap_sc_len; ld a1, 0(t1); li a2, 0\n" ++
  "  la a3, baap_item_off; la a4, baap_item_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbaap_fail\n" ++
  "  la t0, baap_item_len; ld t0, 0(t0); li t1, 32; bgtu t0, t1, .Lbaap_fail\n" ++
  "  la t0, baap_slot; li t1, 0\n" ++
  ".Lbaap_slot_zero:\n" ++
  "  li t2, 32; beq t1, t2, .Lbaap_slot_zero_done\n" ++
  "  add t3, t0, t1; sb zero, 0(t3); addi t1, t1, 1; j .Lbaap_slot_zero\n" ++
  ".Lbaap_slot_zero_done:\n" ++
  "  la t0, baap_item_len; ld t1, 0(t0); li t2, 32; sub t2, t2, t1; la t3, baap_slot; add t3, t3, t2\n" ++
  "  la t0, baap_sc_ptr; ld t0, 0(t0); la t2, baap_item_off; ld t2, 0(t2); add t0, t0, t2\n" ++
  ".Lbaap_slot_cp:\n" ++
  "  beqz t1, .Lbaap_slot_done\n" ++
  "  lbu t2, 0(t0); sb t2, 0(t3); addi t0, t0, 1; addi t3, t3, 1; addi t1, t1, -1; j .Lbaap_slot_cp\n" ++
  ".Lbaap_slot_done:\n" ++
  "  la t0, baap_sc_ptr; ld t0, 0(t0); la t1, baap_item_off; ld t1, 0(t1); add t0, t0, t1\n" ++
  "  la t1, baap_item_len; ld t1, 0(t1); mv a0, t0; mv a1, t1; li a2, 1\n" ++
  "  la a3, baap_slot_changes_off; la a4, baap_slot_changes_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbaap_fail\n" ++
  "  la t0, baap_sc_ptr; ld t0, 0(t0); la t1, baap_item_off; ld t1, 0(t1); add t0, t0, t1\n" ++
  "  la t1, baap_slot_changes_off; ld t1, 0(t1); add t0, t0, t1; la t2, baap_slot_changes_ptr; sd t0, 0(t2)\n" ++
  "  la t1, baap_slot_changes_len; ld a1, 0(t1); mv a0, t0; la a2, baap_slot_changes_count\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lbaap_fail\n" ++
  "  la t0, baap_slot_changes_count; ld t0, 0(t0); beqz t0, .Lbaap_fail\n" ++
  "  addi a2, t0, -1; la t1, baap_slot_changes_ptr; ld a0, 0(t1); la t1, baap_slot_changes_len; ld a1, 0(t1)\n" ++
  "  la a3, baap_item_off; la a4, baap_item_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbaap_fail\n" ++
  "  la t0, baap_slot_changes_ptr; ld t0, 0(t0); la t1, baap_item_off; ld t1, 0(t1); add t0, t0, t1\n" ++
  "  la t1, baap_item_len; ld t1, 0(t1); mv a0, t0; mv a1, t1; li a2, 1; la a3, baap_val_off; la a4, baap_val_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbaap_fail\n" ++
  "  la t0, baap_val_len; ld t0, 0(t0); li t1, 32; bgtu t0, t1, .Lbaap_fail\n" ++
  "  la t1, baap_slot_changes_ptr; ld t1, 0(t1); la t2, baap_item_off; ld t2, 0(t2); add t1, t1, t2\n" ++
  "  la t2, baap_val_off; ld t2, 0(t2); add a3, t1, t2\n" ++
  "  mv a0, s6; mv a1, s7; la a2, baap_slot; mv a4, t0; la a5, baap_tmp2; la a6, baap_tmp2_len\n" ++
  "  jal ra, account_apply_storage_slot\n" ++
  "  bnez a0, .Lbaap_fail\n" ++
  "  la s6, baap_tmp2; la t0, baap_tmp2_len; ld s7, 0(t0)\n" ++
  "  # Apply nonce first if present.\n" ++
  ".Lbaap_nonce:\n" ++
  "  la t0, baap_nonce_len; ld t0, 0(t0); li t1, -1; beq t0, t1, .Lbaap_balance\n" ++
  "  mv a0, s6; mv a1, s7; li a2, 0\n" ++
  "  la a3, baap_nonce; mv a4, t0; la a5, baap_tmp; la a6, baap_tmp_len\n" ++
  "  jal ra, account_set_uint_field\n" ++
  "  bnez a0, .Lbaap_fail\n" ++
  "  la s6, baap_tmp; la t0, baap_tmp_len; ld s7, 0(t0)\n" ++
  ".Lbaap_balance:\n" ++
  "  # Apply balance if present; otherwise copy the current account to the final output.\n" ++
  "  la t0, baap_bal_len; ld t0, 0(t0); li t1, -1; beq t0, t1, .Lbaap_copy_current\n" ++
  "  mv a0, s6; mv a1, s7; li a2, 1\n" ++
  "  la a3, baap_bal; mv a4, t0; mv a5, s4; mv a6, s5\n" ++
  "  jal ra, account_set_uint_field\n" ++
  "  j .Lbaap_ret\n" ++
  ".Lbaap_copy_current:\n" ++
  "  mv a0, s4; mv a1, s6; mv a2, s7\n" ++
  "  jal ra, mset_memcpy\n" ++
  "  sd s7, 0(s5)\n" ++
  "  li a0, 0\n" ++
  "  j .Lbaap_ret\n" ++
  ".Lbaap_fail:\n" ++
  "  li a0, 1\n" ++
  ".Lbaap_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  addi sp, sp, 96\n" ++
  "  ret"

/-- `zisk_bal_account_apply_post_fields`: probe BuildUnit.
    Input layout (file maps to INPUT+8 at 0x40000000):
      +8  account RLP length (u64)
      +16 AccountChanges RLP length (u64)
      +24 account RLP bytes, padded to 8 bytes
      then AccountChanges RLP bytes
    Output layout:
      OUTPUT+0   : new account RLP length
      OUTPUT+8   : new account RLP bytes
      OUTPUT+248 : status -/
def ziskBalAccountApplyPostFieldsPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t0, 0x40000000\n" ++
  "  ld a1, 8(t0)                # account_len\n" ++
  "  ld a3, 16(t0)               # AccountChanges len\n" ++
  "  addi a0, t0, 24             # account ptr\n" ++
  "  add a2, a0, a1              # AccountChanges ptr after padded account\n" ++
  "  addi a2, a2, 7; andi a2, a2, -8\n" ++
  "  li a4, 0xa0010008           # out account bytes at OUTPUT+8\n" ++
  "  li a5, 0xa0010000           # out account length at OUTPUT+0\n" ++
  "  jal ra, bal_account_apply_post_fields\n" ++
  "  li t0, 0xa00100f8; sd a0, 0(t0)   # status at OUTPUT+248\n" ++
  "  j .Lbaap_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  rlpEncodeUintBeFunction ++ "\n" ++
  rlpEncodeBytesFunction ++ "\n" ++
  rlpEncodeListPrefixFunction ++ "\n" ++
  bytesToNibblesFunction ++ "\n" ++
  hpEncodeNibblesFunction ++ "\n" ++
  zkvmKeccak256Function ++ "\n" ++
  singleLeafTrieRootFunction ++ "\n" ++
  storageRootSingleSlotFunction ++ "\n" ++
  rlpItemSizeFunction ++ "\n" ++
  rlpItemSpanFunction ++ "\n" ++
  msetMemcpyFunction ++ "\n" ++
  mptSpliceSlotFunction ++ "\n" ++
  accountSetStorageRootFunction ++ "\n" ++
  accountApplyStorageSlotFunction ++ "\n" ++
  accountSetUintFieldFunction ++ "\n" ++
  balAccountPostFieldsFunction ++ "\n" ++
  balAccountApplyPostFieldsFunction ++ "\n" ++
  ".Lbaap_pdone:"

def ziskBalAccountApplyPostFieldsDataSection : String :=
  ziskAccountAddBalanceDataSection ++ "\n" ++
  ziskBalAccountPostFieldsDataSection ++ "\n" ++
  ".balign 8\n" ++
  "sltr_field_len:\n  .zero 8\n" ++
  "sltr_nibble_count:\n  .zero 8\n" ++
  "sltr_hp_len:\n  .zero 8\n" ++
  "sltr_cursor:\n  .zero 8\n" ++
  "sltr_total_payload:\n  .zero 8\n" ++
  "sltr_nibbles:\n  .zero 2048\n" ++
  "sltr_hp_buf:\n  .zero 1024\n" ++
  "sltr_payload_buf:\n  .zero 16384\n" ++
  "sltr_node_buf:\n  .zero 16384\n" ++
  ".balign 32\n" ++
  "srss_key:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "srss_rlpval:\n  .zero 40\n" ++
  "srss_rlpval_len:\n  .zero 8\n" ++
  "asr_ref:\n  .zero 40\n" ++
  "aps_off:\n  .zero 8\n" ++
  "aps_len:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "aps_newsroot:\n  .zero 32\n" ++
  "aps_empty_root:\n" ++
  "  .byte 0x56, 0xe8, 0x1f, 0x17, 0x1b, 0xcc, 0x55, 0xa6\n" ++
  "  .byte 0xff, 0x83, 0x45, 0xe6, 0x92, 0xc0, 0xf8, 0x6e\n" ++
  "  .byte 0x5b, 0x48, 0xe0, 0x1b, 0x99, 0x6c, 0xad, 0xc0\n" ++
  "  .byte 0x01, 0x62, 0x2f, 0xb5, 0xe3, 0x63, 0xb4, 0x21\n" ++
  ".balign 8\n" ++
  "baap_bal_len:\n  .zero 8\n" ++
  "baap_nonce_len:\n  .zero 8\n" ++
  "baap_tmp_len:\n  .zero 8\n" ++
  "baap_tmp2_len:\n  .zero 8\n" ++
  "baap_sc_off:\n  .zero 8\n" ++
  "baap_sc_len:\n  .zero 8\n" ++
  "baap_sc_ptr:\n  .zero 8\n" ++
  "baap_sc_count:\n  .zero 8\n" ++
  "baap_item_off:\n  .zero 8\n" ++
  "baap_item_len:\n  .zero 8\n" ++
  "baap_slot_changes_off:\n  .zero 8\n" ++
  "baap_slot_changes_len:\n  .zero 8\n" ++
  "baap_slot_changes_ptr:\n  .zero 8\n" ++
  "baap_slot_changes_count:\n  .zero 8\n" ++
  "baap_val_off:\n  .zero 8\n" ++
  "baap_val_len:\n  .zero 8\n" ++
  "baap_code_list_off:\n  .zero 8\n" ++
  "baap_code_list_len:\n  .zero 8\n" ++
  "baap_code_list_ptr:\n  .zero 8\n" ++
  "baap_code_count:\n  .zero 8\n" ++
  "baap_code_item_ptr:\n  .zero 8\n" ++
  "baap_code_off:\n  .zero 8\n" ++
  "baap_code_len:\n  .zero 8\n" ++
  "baap_tmp3_len:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "baap_bal:\n  .zero 32\n" ++
  "baap_nonce:\n  .zero 32\n" ++
  "baap_slot:\n  .zero 32\n" ++
  "baap_code_hash:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "baap_tmp:\n  .zero 512\n" ++
  "baap_tmp2:\n  .zero 512\n" ++
  "baap_tmp3:\n  .zero 512\n" ++
  "baap_out_pad:\n  .zero 8"

def ziskBalAccountApplyPostFieldsProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBalAccountApplyPostFieldsPrologue
  dataAsm     := ziskBalAccountApplyPostFieldsDataSection
}

end EvmAsm.Codegen
