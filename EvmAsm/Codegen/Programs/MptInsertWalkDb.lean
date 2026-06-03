/-
  EvmAsm.Codegen.Programs.MptInsertWalkDb

  mpt_insert_walk_db (bead evm-asm-fhsxz.2.4.2.6.5): the DB-aware divergence
  walk -- identical classification to mpt_insert_walk (Programs/MptInsertWalk),
  but every node hash is resolved via `mpt_node_resolve` (witness SSZ section
  THEN the appendable node DB) and the recorded node pointers are ABSOLUTE
  (a multi-change ancestor can live in the DB, not the witness).

  This is the insert analogue of mpt_set_record_walk_db (Programs/MptSetAcc),
  and is what mpt_insert_acc descends with so that an insert change in
  mpt_state_root sees the new nodes appended by prior changes.

  meta_out / stack_out layout matches mpt_insert_walk EXCEPT the node pointers
  are absolute (stack record +0 = node_ptr_ABS; meta +24 = terminal_ptr_ABS).
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.MptInsertWalk
import EvmAsm.Codegen.Programs.MptSetAcc

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## mpt_insert_walk_db -- classify divergence, resolving via witness+DB.

    ABI matches mpt_insert_walk (a0=root_hash, a1=witness, a2=witness_len,
    a3=path, a4=path_len, a5=stack_out, a6=meta_out -> a0 = 0/1/2), but node
    pointers are ABSOLUTE. The node DB (mset_db_*) must be initialised by the
    caller (mpt_state_root / the probe). -/
def mptInsertWalkDbFunction : String :=
  "mpt_insert_walk_db:\n" ++
  "  addi sp, sp, -96\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  sd s8, 72(sp); sd s9, 80(sp)\n" ++
  "  mv s0, a1                   # witness ptr\n" ++
  "  mv s1, a2                   # witness_len\n" ++
  "  mv s2, a3                   # path ptr\n" ++
  "  mv s3, a4                   # path_len\n" ++
  "  mv s4, a5                   # stack_out cursor\n" ++
  "  mv s5, a6                   # meta_out\n" ++
  "  li s9, 0                    # depth\n" ++
  "  # EMPTY_TRIE_ROOT? (root_hash still in a0) -> case 3.\n" ++
  "  la t2, iw_empty_trie_root\n" ++
  "  ld t3, 0(a0); ld t4, 0(t2); bne t3, t4, .Liwd_resolve_root\n" ++
  "  ld t3, 8(a0); ld t4, 8(t2); bne t3, t4, .Liwd_resolve_root\n" ++
  "  ld t3, 16(a0); ld t4, 16(t2); bne t3, t4, .Liwd_resolve_root\n" ++
  "  ld t3, 24(a0); ld t4, 24(t2); bne t3, t4, .Liwd_resolve_root\n" ++
  "  li t5, 3; j .Liwd_empty\n" ++
  ".Liwd_resolve_root:\n" ++
  "  mv a2, a0                   # hash ptr = root_hash\n" ++
  "  mv a0, s0; mv a1, s1\n" ++
  "  la a3, iwd_ptr; la a4, iwd_len\n" ++
  "  jal ra, mpt_node_resolve\n" ++
  "  bnez a0, .Liwd_miss\n" ++
  "  la t0, iwd_ptr; ld s7, 0(t0)   # absolute node ptr\n" ++
  "  la t0, iwd_len; ld s8, 0(t0)\n" ++
  "  li s6, 0\n" ++
  ".Liwd_loop:\n" ++
  "  mv a0, s7; mv a1, s8\n" ++
  "  jal ra, mpt_node_kind\n" ++
  "  beqz a0, .Liwd_branch\n" ++
  "  li t0, 1; beq a0, t0, .Liwd_extension\n" ++
  "  li t0, 2; beq a0, t0, .Liwd_leaf\n" ++
  "  j .Liwd_parse_fail\n" ++
  ".Liwd_branch:\n" ++
  "  beq s6, s3, .Liwd_branch_value\n" ++
  "  add t0, s2, s6; lbu t1, 0(t0)       # nibble\n" ++
  "  sd s7,  0(s4)               # node_ptr ABSOLUTE\n" ++
  "  sd s8,  8(s4); sd zero, 16(s4); sd t1, 24(s4)\n" ++
  "  addi s4, s4, 32; addi s9, s9, 1\n" ++
  "  mv a0, s7; mv a1, s8; mv a2, t1\n" ++
  "  la a3, mw_child_offset; la a4, mw_child_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  addi s6, s6, 1\n" ++
  "  bnez a0, .Liwd_parse_fail\n" ++
  "  la t0, mw_child_length; ld t1, 0(t0)\n" ++
  "  beqz t1, .Liwd_branch_empty\n" ++
  "  li t2, 32\n" ++
  "  beq t1, t2, .Liwd_branch_hash\n" ++
  "  la t0, mw_child_offset; ld t2, 0(t0)\n" ++
  "  add s7, s7, t2\n" ++
  "  mv s8, t1\n" ++
  "  j .Liwd_loop\n" ++
  ".Liwd_branch_hash:\n" ++
  "  # copy child hash to iwd_hash, resolve via witness+DB.\n" ++
  "  la t0, mw_child_offset; ld t1, 0(t0); add t2, s7, t1\n" ++
  "  la t3, iwd_hash\n" ++
  "  ld t4,  0(t2); sd t4,  0(t3)\n" ++
  "  ld t4,  8(t2); sd t4,  8(t3)\n" ++
  "  ld t4, 16(t2); sd t4, 16(t3)\n" ++
  "  ld t4, 24(t2); sd t4, 24(t3)\n" ++
  "  mv a0, s0; mv a1, s1; la a2, iwd_hash\n" ++
  "  la a3, iwd_ptr; la a4, iwd_len\n" ++
  "  jal ra, mpt_node_resolve\n" ++
  "  bnez a0, .Liwd_miss\n" ++
  "  la t0, iwd_ptr; ld s7, 0(t0); la t0, iwd_len; ld s8, 0(t0)\n" ++
  "  j .Liwd_loop\n" ++
  ".Liwd_branch_empty:\n" ++
  "  addi s4, s4, -32\n" ++
  "  addi s9, s9, -1\n" ++
  "  li t5, 0\n" ++
  "  addi s6, s6, -1\n" ++
  "  li t6, 0\n" ++
  "  j .Liwd_record\n" ++
  ".Liwd_branch_value:\n" ++
  "  li t5, 5\n" ++
  "  li t6, 0\n" ++
  "  j .Liwd_record\n" ++
  ".Liwd_extension:\n" ++
  "  mv a0, s7; mv a1, s8; li a2, 0\n" ++
  "  la a3, mw_path_offset; la a4, mw_path_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Liwd_parse_fail\n" ++
  "  la t0, mw_path_offset; ld t1, 0(t0); add a0, s7, t1\n" ++
  "  la t0, mw_path_length; ld a1, 0(t0)\n" ++
  "  la a2, mw_nibble_buf; la a3, mw_nibble_count; la a4, mw_is_leaf\n" ++
  "  jal ra, hp_decode_nibbles\n" ++
  "  bnez a0, .Liwd_parse_fail\n" ++
  "  la t0, mw_is_leaf; ld t1, 0(t0); bnez t1, .Liwd_parse_fail\n" ++
  "  la t0, mw_nibble_count; ld t1, 0(t0)    # ext nibble count\n" ++
  "  sub t2, s3, s6              # remaining\n" ++
  "  mv t3, t1\n" ++
  "  bgeu t2, t1, .Liwd_ext_lim_ok\n" ++
  "  mv t3, t2\n" ++
  ".Liwd_ext_lim_ok:\n" ++
  "  la t4, mw_nibble_buf\n" ++
  "  add t5, s2, s6\n" ++
  "  li t6, 0\n" ++
  ".Liwd_ext_cmp:\n" ++
  "  beq t6, t3, .Liwd_ext_cmp_done\n" ++
  "  add a0, t4, t6; lbu a1, 0(a0)\n" ++
  "  add a0, t5, t6; lbu a2, 0(a0)\n" ++
  "  bne a1, a2, .Liwd_ext_cmp_done\n" ++
  "  addi t6, t6, 1\n" ++
  "  j .Liwd_ext_cmp\n" ++
  ".Liwd_ext_cmp_done:\n" ++
  "  bne t6, t1, .Liwd_ext_split\n" ++
  "  bgtu t1, t2, .Liwd_ext_split\n" ++
  "  # full extension match: push it (ABS) and descend into child (item 1).\n" ++
  "  sd s7,  0(s4); sd s8,  8(s4)\n" ++
  "  li a1, 1; sd a1, 16(s4); sd zero, 24(s4)\n" ++
  "  addi s4, s4, 32; addi s9, s9, 1\n" ++
  "  add s6, s6, t1\n" ++
  "  mv a0, s7; mv a1, s8; li a2, 1\n" ++
  "  la a3, mw_child_offset; la a4, mw_child_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Liwd_parse_fail\n" ++
  "  la t0, mw_child_length; ld t1, 0(t0)\n" ++
  "  la t0, mw_child_offset; ld t2, 0(t0)\n" ++
  "  add t3, s7, t2\n" ++
  "  li t4, 32\n" ++
  "  beq t1, t4, .Liwd_ext_hash\n" ++
  "  mv s7, t3\n" ++
  "  mv s8, t1\n" ++
  "  j .Liwd_loop\n" ++
  ".Liwd_ext_hash:\n" ++
  "  la t4, iwd_hash\n" ++
  "  ld t5,  0(t3); sd t5,  0(t4)\n" ++
  "  ld t5,  8(t3); sd t5,  8(t4)\n" ++
  "  ld t5, 16(t3); sd t5, 16(t4)\n" ++
  "  ld t5, 24(t3); sd t5, 24(t4)\n" ++
  "  mv a0, s0; mv a1, s1; la a2, iwd_hash\n" ++
  "  la a3, iwd_ptr; la a4, iwd_len\n" ++
  "  jal ra, mpt_node_resolve\n" ++
  "  bnez a0, .Liwd_miss\n" ++
  "  la t0, iwd_ptr; ld s7, 0(t0); la t0, iwd_len; ld s8, 0(t0)\n" ++
  "  j .Liwd_loop\n" ++
  ".Liwd_ext_split:\n" ++
  "  li t5, 2\n" ++
  "  j .Liwd_record\n" ++
  ".Liwd_leaf:\n" ++
  "  mv a0, s7; mv a1, s8; li a2, 0\n" ++
  "  la a3, mw_path_offset; la a4, mw_path_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Liwd_parse_fail\n" ++
  "  la t0, mw_path_offset; ld t1, 0(t0); add a0, s7, t1\n" ++
  "  la t0, mw_path_length; ld a1, 0(t0)\n" ++
  "  la a2, mw_nibble_buf; la a3, mw_nibble_count; la a4, mw_is_leaf\n" ++
  "  jal ra, hp_decode_nibbles\n" ++
  "  bnez a0, .Liwd_parse_fail\n" ++
  "  la t0, mw_is_leaf; ld t1, 0(t0); li t2, 1; bne t1, t2, .Liwd_parse_fail\n" ++
  "  la t0, mw_nibble_count; ld t1, 0(t0)    # leaf key nibble count\n" ++
  "  sub t2, s3, s6              # remaining\n" ++
  "  mv t3, t1\n" ++
  "  bgeu t2, t1, .Liwd_leaf_lim_ok\n" ++
  "  mv t3, t2\n" ++
  ".Liwd_leaf_lim_ok:\n" ++
  "  la t4, mw_nibble_buf\n" ++
  "  add t5, s2, s6\n" ++
  "  li t6, 0\n" ++
  ".Liwd_leaf_cmp:\n" ++
  "  beq t6, t3, .Liwd_leaf_cmp_done\n" ++
  "  add a0, t4, t6; lbu a1, 0(a0)\n" ++
  "  add a0, t5, t6; lbu a2, 0(a0)\n" ++
  "  bne a1, a2, .Liwd_leaf_cmp_done\n" ++
  "  addi t6, t6, 1\n" ++
  "  j .Liwd_leaf_cmp\n" ++
  ".Liwd_leaf_cmp_done:\n" ++
  "  bne t6, t1, .Liwd_leaf_split\n" ++
  "  bne t1, t2, .Liwd_leaf_split\n" ++
  "  li t5, 4\n" ++
  "  j .Liwd_record\n" ++
  ".Liwd_leaf_split:\n" ++
  "  li t5, 1\n" ++
  "  j .Liwd_record\n" ++
  ".Liwd_record:\n" ++
  "  sd s9, 0(s5)               # depth\n" ++
  "  sd s6, 8(s5)               # consumed\n" ++
  "  sd t5, 16(s5)              # case\n" ++
  "  sd s7, 24(s5)              # terminal_ptr ABSOLUTE\n" ++
  "  sd s8, 32(s5)              # terminal_len\n" ++
  "  sd t6, 40(s5)              # match_len\n" ++
  "  li a0, 0\n" ++
  "  j .Liwd_ret\n" ++
  ".Liwd_empty:\n" ++
  "  sd zero, 0(s5); sd zero, 8(s5); sd t5, 16(s5)\n" ++
  "  sd zero, 24(s5); sd zero, 32(s5); sd zero, 40(s5)\n" ++
  "  li a0, 0\n" ++
  "  j .Liwd_ret\n" ++
  ".Liwd_miss:\n" ++
  "  li a0, 1\n" ++
  "  j .Liwd_ret\n" ++
  ".Liwd_parse_fail:\n" ++
  "  li a0, 2\n" ++
  ".Liwd_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp); ld s9, 80(sp)\n" ++
  "  addi sp, sp, 96\n" ++
  "  ret"

/-- `zisk_mpt_insert_walk_db`: probe. Initialises the node DB to empty, then
    runs mpt_insert_walk_db with the same input layout as zisk_mpt_insert_walk
    (so the iw vectors verify the classification fields, which are
    DB/layout-independent; the absolute ptr fields are validated end-to-end by
    mpt_insert_acc). Output: status@0, meta@8 (48 B), stack@128. -/
def ziskMptInsertWalkDbPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  # init node DB empty\n" ++
  "  la t0, mset_db_count; sd zero, 0(t0)\n" ++
  "  la t0, mset_db_data; la t1, mset_db_top; sd t0, 0(t1)\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld t6, 8(a7)                # witness_len\n" ++
  "  ld t5, 16(a7)               # path_len\n" ++
  "  ld t4, 24(a7)               # new_value_len\n" ++
  "  addi a0, a7, 32             # root_hash ptr\n" ++
  "  addi a3, a7, 64             # path ptr\n" ++
  "  add t3, t5, t4\n" ++
  "  addi t3, t3, 7\n" ++
  "  andi t3, t3, -8\n" ++
  "  add a1, a3, t3              # witness ptr\n" ++
  "  mv a2, t6                   # witness_len\n" ++
  "  mv a4, t5                   # path_len\n" ++
  "  li a5, 0xa0010080           # stack_out at OUTPUT+128\n" ++
  "  li a6, 0xa0010008           # meta_out at OUTPUT+8\n" ++
  "  jal ra, mpt_insert_walk_db\n" ++
  "  li t0, 0xa0010000; sd a0, 0(t0)\n" ++
  "  j .Liwd_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  witnessLookupByHashFunction ++ "\n" ++
  nodeDbLookupFunction ++ "\n" ++
  mptResolveCacheResetFunction ++ "\n" ++
  mptNodeResolveFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  mptNodeKindFunction ++ "\n" ++
  hpDecodeNibblesFunction ++ "\n" ++
  mptInsertWalkDbFunction ++ "\n" ++
  ".Liwd_pdone:"

def ziskMptInsertWalkDbDataSection : String :=
  ziskMptInsertWalkDataSection ++ "\n" ++
  -- mpt_node_resolve scratch + the node DB (mset_res_*, mset_db_*)
  ".balign 8\n" ++
  "mset_res_off:\n  .zero 8\n" ++
  "mset_res_len:\n  .zero 8\n" ++
  ".balign 8\n" ++
  "iwd_ptr:\n  .zero 8\n" ++
  "iwd_len:\n  .zero 8\n" ++
  ".balign 8\n" ++
  "iwd_hash:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "mset_db_count:\n  .zero 8\n" ++
  "mset_db_top:\n  .zero 8\n" ++
  ".balign 8\n" ++
  "mset_db_hash:\n  .zero 32\n" ++
  mptResolveCacheDataSection ++ "\n" ++
  ".balign 8\n" ++
  "mset_db_data:\n  .zero 8388608"

def ziskMptInsertWalkDbProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskMptInsertWalkDbPrologue
  dataAsm     := ziskMptInsertWalkDbDataSection
}

end EvmAsm.Codegen
