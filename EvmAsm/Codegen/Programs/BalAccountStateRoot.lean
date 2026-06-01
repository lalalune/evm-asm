/-
  EvmAsm.Codegen.Programs.BalAccountStateRoot

  Bridge BAL account descriptor preparation into `mpt_state_root_ins`: given a
  pre-state root/witness, a BAL AccountChanges list, and caller-supplied
  pre-account records, recompute the post state root for those account changes.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.BalAccountDescriptorArray
import EvmAsm.Codegen.Programs.MptStateRootIns

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## bal_account_state_root -- BAL descriptors + mpt_state_root_ins

    a0 = root_hash ptr        a1 = witness ptr       a2 = witness length
    a3 = BAL list ptr         a4 = BAL list length   a5 = account records ptr
    a6 = n records/items      a7 = out root ptr
    a0 (output) = 0 ok / nonzero failure.

    Account records use `bal_account_descriptor_array`'s 24-byte layout:
      +0 account_ptr | +8 account_len | +16 is_insert. -/
def balAccountStateRootFunction : String :=
  "bal_account_state_root:\n" ++
  "  addi sp, sp, -96\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  mv s0, a0                   # root hash ptr\n" ++
  "  mv s1, a1                   # witness ptr\n" ++
  "  mv s2, a2                   # witness len\n" ++
  "  mv s3, a5                   # account records\n" ++
  "  mv s4, a6                   # n\n" ++
  "  mv s5, a7                   # out root\n" ++
  "  mv a0, a3; mv a1, a4; mv a2, s3; mv a3, s4\n" ++
  "  la a4, basr_desc; la a5, basr_paths; la a6, basr_values\n" ++
  "  jal ra, bal_account_descriptor_array\n" ++
  "  bnez a0, .Lbasr_ret\n" ++
  "  mv a0, s0; mv a1, s1; mv a2, s2; la a3, basr_desc; mv a4, s4; mv a5, s5\n" ++
  "  jal ra, mpt_state_root_ins\n" ++
  ".Lbasr_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  addi sp, sp, 96\n" ++
  "  ret"

/-- `zisk_bal_account_state_root`: probe BuildUnit.
    Input layout (file maps to INPUT+8 at 0x40000000):
      +8  witness length (u64)
      +16 n (u64)
      +24 BAL list length (u64)
      +32 root hash (32 bytes)
      +64 table: n x (account_len:u64, is_insert:u64)
      then account RLP blobs, each padded to 8 bytes
      then BAL AccountChanges list bytes, padded to 8 bytes
      then witness section
    Output: OUTPUT+0 = final root, OUTPUT+32 = status. -/
def ziskBalAccountStateRootPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t0, 0x40000000\n" ++
  "  ld a2, 8(t0)                # witness len\n" ++
  "  ld a6, 16(t0)               # n\n" ++
  "  ld a4, 24(t0)               # BAL list len\n" ++
  "  addi a0, t0, 32             # root hash ptr\n" ++
  "  addi t1, t0, 64             # input table\n" ++
  "  slli t2, a6, 4; add t3, t1, t2   # account blob cursor\n" ++
  "  la a5, basr_records         # account records out\n" ++
  "  li t4, 0\n" ++
  ".Lbasrp_records:\n" ++
  "  beq t4, a6, .Lbasrp_records_done\n" ++
  "  slli t5, t4, 4; add t5, t1, t5\n" ++
  "  ld s6, 0(t5)                # account len\n" ++
  "  ld s7, 8(t5)                # is_insert\n" ++
  "  slli t5, t4, 4; slli t6, t4, 3; add t5, t5, t6; add t5, a5, t5\n" ++
  "  sd t3, 0(t5); sd s6, 8(t5); sd s7, 16(t5)\n" ++
  "  add t3, t3, s6; addi t3, t3, 7; andi t3, t3, -8\n" ++
  "  addi t4, t4, 1\n" ++
  "  j .Lbasrp_records\n" ++
  ".Lbasrp_records_done:\n" ++
  "  mv a3, t3                   # BAL list ptr\n" ++
  "  add t3, t3, a4; addi t3, t3, 7; andi t3, t3, -8\n" ++
  "  mv a1, t3                   # witness ptr\n" ++
  "  li a7, 0xa0010000           # out root\n" ++
  "  jal ra, bal_account_state_root\n" ++
  "  li t0, 0xa0010020; sd a0, 0(t0)\n" ++
  "  j .Lbasr_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  bytesToNibblesFunction ++ "\n" ++
  witnessLookupByHashFunction ++ "\n" ++
  nodeDbLookupFunction ++ "\n" ++
  nodeDbAppendFunction ++ "\n" ++
  mptNodeResolveFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  mptNodeKindFunction ++ "\n" ++
  hpDecodeNibblesFunction ++ "\n" ++
  mptSetRecordWalkDbFunction ++ "\n" ++
  mptInsertWalkDbFunction ++ "\n" ++
  hpEncodeNibblesFunction ++ "\n" ++
  rlpEncodeUintBeFunction ++ "\n" ++
  rlpEncodeBytesFunction ++ "\n" ++
  rlpEncodeListPrefixFunction ++ "\n" ++
  mptLeafNodeEncodeFromNibblesFunction ++ "\n" ++
  mptNodeSlotEncodeFunction ++ "\n" ++
  rlpItemSizeFunction ++ "\n" ++
  rlpItemSpanFunction ++ "\n" ++
  msetMemcpyFunction ++ "\n" ++
  mptSpliceSlotFunction ++ "\n" ++
  mptLeafExtractFunction ++ "\n" ++
  mptExtensionNodeEncodeFunction ++ "\n" ++
  accountSetUintFieldFunction ++ "\n" ++
  balAccountPathFunction ++ "\n" ++
  balAccountPostFieldsFunction ++ "\n" ++
  balAccountApplyPostFieldsFunction ++ "\n" ++
  balAccountChangeValueFunction ++ "\n" ++
  balAccountChangeDescriptorFunction ++ "\n" ++
  balAccountDescriptorArrayFunction ++ "\n" ++
  mptSetAccFunction ++ "\n" ++
  mptInsertAccFunction ++ "\n" ++
  mptStateRootInsFunction ++ "\n" ++
  balAccountStateRootFunction ++ "\n" ++
  ".Lbasr_pdone:"

/-- Data section combines the MPT state-root driver scratch with only the
    BAL/account-rewrite labels that are not already provided by MPT scratch. -/
def ziskBalAccountStateRootDataSection : String :=
  ziskMptStateRootInsDataSection ++ "\n" ++
  ".balign 8\n" ++
  "aab_enc_len:\n  .zero 8\n" ++
  ".balign 8\n" ++
  "aab_enc:\n  .zero 64\n" ++
  ".balign 8\n" ++
  "bpf_list_off:\n  .zero 8\n" ++
  "bpf_list_len:\n  .zero 8\n" ++
  "bpf_list_ptr:\n  .zero 8\n" ++
  "bpf_count:\n  .zero 8\n" ++
  "bpf_item_off:\n  .zero 8\n" ++
  "bpf_item_len:\n  .zero 8\n" ++
  "bpf_item_ptr:\n  .zero 8\n" ++
  "bpf_val_off:\n  .zero 8\n" ++
  "bpf_val_len:\n  .zero 8\n" ++
  "baap_bal_len:\n  .zero 8\n" ++
  "baap_nonce_len:\n  .zero 8\n" ++
  "baap_tmp_len:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "baap_bal:\n  .zero 32\n" ++
  "baap_nonce:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "baap_tmp:\n  .zero 512\n" ++
  "bacp_off:\n  .zero 8\n" ++
  "bacp_len:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "bacp_hash:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "baacd_value_len:\n  .zero 8\n" ++
  "baada_item_off:\n  .zero 8\n" ++
  "baada_item_len:\n  .zero 8\n" ++
  "basr_records:\n  .zero 4096\n" ++
  "basr_desc:\n  .zero 4096\n" ++
  "basr_paths:\n  .zero 8192\n" ++
  "basr_values:\n  .zero 16384\n" ++
  "basr_pad:\n  .zero 8"

def ziskBalAccountStateRootProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBalAccountStateRootPrologue
  dataAsm     := ziskBalAccountStateRootDataSection
}

end EvmAsm.Codegen
