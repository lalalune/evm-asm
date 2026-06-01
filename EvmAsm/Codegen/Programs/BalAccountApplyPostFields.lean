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
  "  # Apply nonce first if present.\n" ++
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
  rlpEncodeListPrefixFunction ++ "\n" ++
  rlpItemSizeFunction ++ "\n" ++
  rlpItemSpanFunction ++ "\n" ++
  msetMemcpyFunction ++ "\n" ++
  mptSpliceSlotFunction ++ "\n" ++
  accountSetUintFieldFunction ++ "\n" ++
  balAccountPostFieldsFunction ++ "\n" ++
  balAccountApplyPostFieldsFunction ++ "\n" ++
  ".Lbaap_pdone:"

def ziskBalAccountApplyPostFieldsDataSection : String :=
  ziskAccountAddBalanceDataSection ++ "\n" ++
  ziskBalAccountPostFieldsDataSection ++ "\n" ++
  ".balign 8\n" ++
  "baap_bal_len:\n  .zero 8\n" ++
  "baap_nonce_len:\n  .zero 8\n" ++
  "baap_tmp_len:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "baap_bal:\n  .zero 32\n" ++
  "baap_nonce:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "baap_tmp:\n  .zero 512\n" ++
  "baap_out_pad:\n  .zero 8"

def ziskBalAccountApplyPostFieldsProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBalAccountApplyPostFieldsPrologue
  dataAsm     := ziskBalAccountApplyPostFieldsDataSection
}

end EvmAsm.Codegen
