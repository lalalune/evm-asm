/-
  EvmAsm.Codegen.Programs.BalAccountDescriptorArray

  Build an `mpt_state_root_ins` descriptor array from a BAL AccountChanges list
  and caller-supplied pre-account records. This is the list-level adapter above
  the per-item BAL descriptor helpers.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.BalAccountChangeDescriptor

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## bal_account_descriptor_array -- BAL list -> descriptor array

    a0 = BAL AccountChanges list ptr   a1 = BAL AccountChanges list length
    a2 = account records ptr           a3 = n records/items
    a4 = descriptors out ptr           a5 = path arena out ptr
    a6 = value arena out ptr
    a0 (output) = 0 ok / 1 failure.

    Account record layout is 24 bytes per selected BAL item:
      +0 account_ptr | +8 account_len | +16 is_insert.

    Descriptor layout matches `mpt_state_root_ins`, 40 bytes per item. Paths are
    written densely as 64-byte nibble arrays. Values are written densely in the
    value arena, each rounded up to an 8-byte boundary before the next value. -/
def balAccountDescriptorArrayFunction : String :=
  "bal_account_descriptor_array:\n" ++
  "  addi sp, sp, -112\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp); sd s8, 72(sp)\n" ++
  "  mv s0, a0                   # BAL list ptr\n" ++
  "  mv s1, a1                   # BAL list len\n" ++
  "  mv s2, a2                   # account records\n" ++
  "  mv s3, a3                   # n\n" ++
  "  mv s4, a4                   # descriptor cursor\n" ++
  "  mv s5, a5                   # path cursor\n" ++
  "  mv s6, a6                   # value cursor\n" ++
  "  li s7, 0                    # i\n" ++
  ".Lbaada_loop:\n" ++
  "  beq s7, s3, .Lbaada_ok\n" ++
  "  mv a0, s0; mv a1, s1; mv a2, s7\n" ++
  "  la a3, baada_item_off; la a4, baada_item_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbaada_ret\n" ++
  "  slli t0, s7, 4; slli t1, s7, 3; add t0, t0, t1; add t0, s2, t0\n" ++
  "  ld a0, 0(t0)                # account ptr\n" ++
  "  ld a1, 8(t0)                # account len\n" ++
  "  ld a4, 16(t0)               # is_insert\n" ++
  "  la t1, baada_item_off; ld t1, 0(t1); add a2, s0, t1\n" ++
  "  la t1, baada_item_len; ld a3, 0(t1)\n" ++
  "  mv a5, s4; mv a6, s5; mv a7, s6\n" ++
  "  jal ra, bal_account_change_descriptor\n" ++
  "  bnez a0, .Lbaada_ret\n" ++
  "  ld s8, 24(s4)               # value length from descriptor\n" ++
  "  addi s4, s4, 40\n" ++
  "  addi s5, s5, 64\n" ++
  "  add s6, s6, s8; addi s6, s6, 7; andi s6, s6, -8\n" ++
  "  addi s7, s7, 1\n" ++
  "  j .Lbaada_loop\n" ++
  ".Lbaada_ok:\n" ++
  "  li a0, 0\n" ++
  ".Lbaada_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp); ld s8, 72(sp)\n" ++
  "  addi sp, sp, 112\n" ++
  "  ret"

/-- `zisk_bal_account_descriptor_array`: probe BuildUnit.
    Input layout (file maps to INPUT+8 at 0x40000000):
      +8  BAL list length (u64)
      +16 n (u64)
      +24 table: n x (account_len:u64, is_insert:u64)
      then account RLP blobs, each padded to 8 bytes
      then BAL AccountChanges list bytes
    Output layout:
      OUTPUT+0   : status
      OUTPUT+8   : descriptor array
      OUTPUT+88  : path arena (for two probe rows)
      OUTPUT+216 : value arena (for compact probe accounts)
      OUTPUT+248 : duplicate status -/
def ziskBalAccountDescriptorArrayPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t0, 0x40000000\n" ++
  "  ld a1, 8(t0)                # BAL list len\n" ++
  "  ld a3, 16(t0)               # n\n" ++
  "  addi t1, t0, 24             # input table\n" ++
  "  slli t2, a3, 4; add t3, t1, t2   # blob cursor after 16*n table\n" ++
  "  la t4, baada_records        # record table out\n" ++
  "  li t5, 0\n" ++
  ".Lbaadap_records:\n" ++
  "  beq t5, a3, .Lbaadap_records_done\n" ++
  "  slli t6, t5, 4; add t6, t1, t6\n" ++
  "  ld a4, 0(t6)                # account len\n" ++
  "  ld a5, 8(t6)                # is_insert\n" ++
  "  slli t6, t5, 4; slli a6, t5, 3; add t6, t6, a6; add t6, t4, t6\n" ++
  "  sd t3, 0(t6); sd a4, 8(t6); sd a5, 16(t6)\n" ++
  "  add t3, t3, a4; addi t3, t3, 7; andi t3, t3, -8\n" ++
  "  addi t5, t5, 1\n" ++
  "  j .Lbaadap_records\n" ++
  ".Lbaadap_records_done:\n" ++
  "  mv a0, t3                   # BAL list ptr\n" ++
  "  la a2, baada_records\n" ++
  "  li a4, 0xa0010008           # descriptors\n" ++
  "  li a5, 0xa0010058           # paths\n" ++
  "  li a6, 0xa00100d8           # values\n" ++
  "  jal ra, bal_account_descriptor_array\n" ++
  "  li t0, 0xa0010000; sd a0, 0(t0)\n" ++
  "  li t0, 0xa00100f8; sd a0, 0(t0)\n" ++
  "  j .Lbaada_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  bytesToNibblesFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  rlpEncodeUintBeFunction ++ "\n" ++
  rlpEncodeListPrefixFunction ++ "\n" ++
  rlpItemSizeFunction ++ "\n" ++
  rlpItemSpanFunction ++ "\n" ++
  msetMemcpyFunction ++ "\n" ++
  mptSpliceSlotFunction ++ "\n" ++
  accountSetUintFieldFunction ++ "\n" ++
  balAccountPathFunction ++ "\n" ++
  balAccountPostFieldsFunction ++ "\n" ++
  balAccountApplyPostFieldsFunction ++ "\n" ++
  balAccountChangeValueFunction ++ "\n" ++
  balAccountChangeDescriptorFunction ++ "\n" ++
  balAccountDescriptorArrayFunction ++ "\n" ++
  ".Lbaada_pdone:"

def ziskBalAccountDescriptorArrayDataSection : String :=
  ziskBalAccountChangeDescriptorDataSection ++ "\n" ++
  ".balign 8\n" ++
  "baada_item_off:\n  .zero 8\n" ++
  "baada_item_len:\n  .zero 8\n" ++
  "baada_records:\n  .zero 768\n" ++
  "baada_pad:\n  .zero 8"

def ziskBalAccountDescriptorArrayProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBalAccountDescriptorArrayPrologue
  dataAsm     := ziskBalAccountDescriptorArrayDataSection
}

end EvmAsm.Codegen
