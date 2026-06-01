/-
  EvmAsm.Codegen.Programs.BalGasValid

  bal_gas_valid (bead evm-asm-fhsxz.2.4.2.5, task #23): the EIP-7928 block-access-
  list gas-limit rule — the binding constraint that makes the Step-2 verdict reject
  blocks like `bal_gas_limit_boundary[below_boundary]` (which header-validation and
  the state recompute cannot catch, since it is a semantic rule not reflected in any
  header field or the state root).

  Spec (execution-specs amsterdam/block_access_lists.py:validate_block_access_list_gas_limit):
    bal_items = Σ over accounts of (1 + #unique storage slots)
    INVALID iff bal_items > block_gas_limit // BLOCK_ACCESS_LIST_ITEM (=2000).
  The BAL encoder makes `storage_reads` DISJOINT from `storage_changes` (it omits
  read slots already in storage_changes), so #unique slots = len(storage_changes) +
  len(storage_reads) — no dedup needed, just element counts.

  BAL RLP = list of AccountChanges; each AccountChanges =
    [address, storage_changes, storage_reads, balance_changes, nonce_changes, code_changes].
  So per account: bal_items += 1 + count(item 1) + count(item 2).

  Division-free test: bal_items > gas_limit/2000  ⟺  bal_items*2000 > gas_limit.

  Composes rlp_item_span (full sub-item spans, for nesting) + rlp_list_count_items.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.RlpRead

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## bal_gas_valid
    a0 = BAL RLP ptr   a1 = BAL RLP length   a2 = block_gas_limit
    a0 (output) = 0 (valid) / 1 (gas-limit exceeded) / 2 (parse error). -/
def balGasValidFunction : String :=
  "bal_gas_valid:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a0                   # BAL ptr\n" ++
  "  mv s1, a1                   # BAL len\n" ++
  "  mv s2, a2                   # gas_limit\n" ++
  "  # n_accounts = rlp_list_count_items(BAL)\n" ++
  "  mv a0, s0; mv a1, s1; la a2, bgv_count\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lbgv_fail\n" ++
  "  la t0, bgv_count; ld s3, 0(t0)    # s3 = n_accounts\n" ++
  "  li s4, 0                          # s4 = bal_items\n" ++
  "  li s5, 0                          # s5 = i\n" ++
  ".Lbgv_loop:\n" ++
  "  beq s5, s3, .Lbgv_done\n" ++
  "  # account span = rlp_item_span(BAL, i)\n" ++
  "  mv a0, s0; mv a1, s1; mv a2, s5; la a3, bgv_off; la a4, bgv_size\n" ++
  "  jal ra, rlp_item_span\n" ++
  "  bnez a0, .Lbgv_fail\n" ++
  "  la t0, bgv_off; ld t1, 0(t0); add s6, s0, t1    # account_ptr\n" ++
  "  la t0, bgv_size; ld t1, 0(t0); la t2, bgv_acctlen; sd t1, 0(t2)  # account_len\n" ++
  "  addi s4, s4, 1                    # +1 for the address\n" ++
  "  # + count(item 1 = storage_changes)\n" ++
  "  mv a0, s6; la t0, bgv_acctlen; ld a1, 0(t0); li a2, 1; la a3, bgv_off; la a4, bgv_size\n" ++
  "  jal ra, rlp_item_span\n" ++
  "  bnez a0, .Lbgv_fail\n" ++
  "  la t0, bgv_off; ld t1, 0(t0); add a0, s6, t1\n" ++
  "  la t0, bgv_size; ld a1, 0(t0); la a2, bgv_count\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lbgv_fail\n" ++
  "  la t0, bgv_count; ld t1, 0(t0); add s4, s4, t1\n" ++
  "  # + count(item 2 = storage_reads)\n" ++
  "  mv a0, s6; la t0, bgv_acctlen; ld a1, 0(t0); li a2, 2; la a3, bgv_off; la a4, bgv_size\n" ++
  "  jal ra, rlp_item_span\n" ++
  "  bnez a0, .Lbgv_fail\n" ++
  "  la t0, bgv_off; ld t1, 0(t0); add a0, s6, t1\n" ++
  "  la t0, bgv_size; ld a1, 0(t0); la a2, bgv_count\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lbgv_fail\n" ++
  "  la t0, bgv_count; ld t1, 0(t0); add s4, s4, t1\n" ++
  "  addi s5, s5, 1; j .Lbgv_loop\n" ++
  ".Lbgv_done:\n" ++
  "  # invalid iff bal_items*2000 > gas_limit\n" ++
  "  li t0, 2000; mul t1, s4, t0\n" ++
  "  bgtu t1, s2, .Lbgv_exceeded\n" ++
  "  li a0, 0; j .Lbgv_ret\n" ++
  ".Lbgv_exceeded:\n" ++
  "  li a0, 1; j .Lbgv_ret\n" ++
  ".Lbgv_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lbgv_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-! ## bgv_u32le -- read a little-endian u32 byte-wise (a0=ptr -> a0). Leaf. -/
def bgvU32leFunction : String :=
  "bgv_u32le:\n" ++
  "  lbu t0, 0(a0)\n" ++
  "  lbu t1, 1(a0); slli t1, t1, 8;  or t0, t0, t1\n" ++
  "  lbu t1, 2(a0); slli t1, t1, 16; or t0, t0, t1\n" ++
  "  lbu t1, 3(a0); slli t1, t1, 24; or t0, t0, t1\n" ++
  "  mv a0, t0\n" ++
  "  ret"

/-! ## bgv_u64le -- read a little-endian u64 byte-wise (a0=ptr -> a0). Leaf. -/
def bgvU64leFunction : String :=
  "bgv_u64le:\n" ++
  "  li t0, 0; li t2, 0\n" ++
  ".Lbgv64:\n" ++
  "  li t3, 8; beq t2, t3, .Lbgv64d\n" ++
  "  add t4, a0, t2; lbu t5, 0(t4); slli t6, t2, 3; sll t5, t5, t6; or t0, t0, t5\n" ++
  "  addi t2, t2, 1; j .Lbgv64\n" ++
  ".Lbgv64d:\n" ++
  "  mv a0, t0; ret"

/-! ## bal_section_info -- locate BAL RLP inside an SszStatelessInput.
    a0 = SSZ_BASE   a1 = out BAL ptr   a2 = out BAL len   a3 = out account count
    a0 (output) = 0 ok / 1 parse error. -/
def balSectionInfoFunction : String :=
  "bal_section_info:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp)\n" ++
  "  mv s0, a0                   # SSZ_BASE\n" ++
  "  mv s3, a1                   # out ptr cell\n" ++
  "  mv s4, a2                   # out len cell\n" ++
  "  mv s5, a3                   # out count cell\n" ++
  "  addi s1, s0, 16             # NPR = SSZ_BASE+16\n" ++
  "  addi s2, s0, 60             # exec_payload = SSZ_BASE+60\n" ++
  "  addi a0, s2, 528; jal ra, bgv_u32le\n" ++
  "  add t0, s2, a0              # bal_start\n" ++
  "  sd t0, 0(s3)\n" ++
  "  addi a0, s1, 4; jal ra, bgv_u32le\n" ++
  "  add t1, s1, a0              # bal_end\n" ++
  "  ld t0, 0(s3); sub t1, t1, t0\n" ++
  "  sd t1, 0(s4)\n" ++
  "  mv a0, t0; mv a1, t1; mv a2, s5\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lbsi_fail\n" ++
  "  li a0, 0; j .Lbsi_ret\n" ++
  ".Lbsi_fail:\n" ++
  "  li a0, 1\n" ++
  ".Lbsi_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-- `zisk_bal_section_info`: probe. Fed the SAME `-i` input as the guest.
    Output: OUTPUT+0 = status, OUTPUT+8 = BAL ptr, OUTPUT+16 = BAL len,
    OUTPUT+24 = account count. -/
def ziskBalSectionInfoPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a0, 0x40000000; addi a0, a0, 18    # SSZ_BASE\n" ++
  "  li a1, 0xa0010008\n" ++
  "  li a2, 0xa0010010\n" ++
  "  li a3, 0xa0010018\n" ++
  "  jal ra, bal_section_info\n" ++
  "  li t0, 0xa0010000; sd a0, 0(t0)\n" ++
  "  j .Lbsi_pdone\n" ++
  rlpItemSizeFunction ++ "\n" ++
  rlpItemSpanFunction ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  bgvU32leFunction ++ "\n" ++
  bgvU64leFunction ++ "\n" ++
  balSectionInfoFunction ++ "\n" ++
  ".Lbsi_pdone:"

/-- `zisk_bal_gas_valid`: probe. Fed the SAME `-i` input as the guest. Navigates
    to the block_access_list section + block_gas_limit and runs bal_gas_valid.
    Output: OUTPUT+0 = result (0 valid / 1 exceeded / 2 parse error). -/
def ziskBalGasValidPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li s0, 0x40000000; addi s0, s0, 18    # SSZ_BASE\n" ++
  "  addi s1, s0, 16                       # NPR = SSZ_BASE+16\n" ++
  "  addi s2, s1, 44                       # exec_payload = NPR+44\n" ++
  "  # bal_off = u32 @ exec_payload+528 ; bal_start = exec_payload + bal_off\n" ++
  "  addi a0, s2, 528; jal ra, bgv_u32le\n" ++
  "  add s3, s2, a0                        # bal_start\n" ++
  "  # bal_end = NPR + (u32 @ NPR+4)\n" ++
  "  addi a0, s1, 4; jal ra, bgv_u32le\n" ++
  "  add s4, s1, a0                        # bal_end\n" ++
  "  sub s4, s4, s3                        # bal_len\n" ++
  "  # gas_limit = u64 @ exec_payload+412\n" ++
  "  addi a0, s2, 412; jal ra, bgv_u64le\n" ++
  "  mv a2, a0                             # gas_limit\n" ++
  "  mv a0, s3; mv a1, s4                  # BAL ptr, len\n" ++
  "  jal ra, bal_gas_valid\n" ++
  "  li t0, 0xa0010000; sd a0, 0(t0)\n" ++
  "  j .Lbgv_pdone\n" ++
  rlpItemSizeFunction ++ "\n" ++
  rlpItemSpanFunction ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  bgvU32leFunction ++ "\n" ++
  bgvU64leFunction ++ "\n" ++
  balGasValidFunction ++ "\n" ++
  ".Lbgv_pdone:"

def ziskBalGasValidDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "bgv_count:\n  .zero 8\n" ++
  "bgv_off:\n  .zero 8\n" ++
  "bgv_size:\n  .zero 8\n" ++
  "bgv_acctlen:\n  .zero 8"

def ziskBalGasValidProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBalGasValidPrologue
  dataAsm     := ziskBalGasValidDataSection
}

def ziskBalSectionInfoProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBalSectionInfoPrologue
  dataAsm     := ziskBalGasValidDataSection
}

end EvmAsm.Codegen
