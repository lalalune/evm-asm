/-
  EvmAsm.Codegen.Programs.AccountApplyStorage

  account_apply_storage_slot (bead evm-asm-fhsxz.2.4.2.5, step c): apply a single
  storage write to an account, producing the new account RLP. This is the per-
  system-contract update the EIP-2935 (history) and EIP-4788 (beacon-roots) block-
  start system calls perform, and the brick that composes the StorageWrite
  primitives into the Step-2 state recompute.

  Given an account [nonce, balance, storageRoot, codeHash] and a (slot_key, value):
    1. read field 2 (storageRoot) via rlp_list_nth_item;
    2. if it is NOT the EMPTY_TRIE_ROOT, return status 1 (conservative miss —
       a non-empty storage trie needs the general storage-trie update, out of the
       single-leaf engine's scope; the verdict then leaves x11 = 0, never a false
       positive). The genesis case both system contracts hit on the first blocks
       (empty prior storage) IS handled;
    3. else new_storage_root = storage_root_single_slot(slot_key, value);
    4. account_set_storage_root(account, new_storage_root) -> new account RLP.

  Composes storage_root_single_slot + account_set_storage_root (StorageWrite) +
  rlp_list_nth_item; all byte work byte-wise (no-misaligned invariant).
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.MptEncode
import EvmAsm.Codegen.Programs.MptSet
import EvmAsm.Codegen.Programs.StorageWrite
import EvmAsm.Codegen.Programs.MptSetAcc
import EvmAsm.Codegen.Programs.MptInsertAcc
import EvmAsm.Codegen.Programs.MptDeleteAcc

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## account_apply_storage_slot
    a0 = account RLP ptr   a1 = account RLP length
    a2 = slot_key ptr (32 B)   a3 = value ptr (minimal-BE word)   a4 = value len
    a5 = out account RLP ptr   a6 = u64 out length ptr
    a0 (output) = 0 (ok) / 1 (non-empty prior storage: conservative) /
                  2 (parse fail). -/
def accountApplyStorageSlotFunction : String :=
  "account_apply_storage_slot:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a0                   # account\n" ++
  "  mv s1, a1                   # account len\n" ++
  "  mv s2, a2                   # slot_key\n" ++
  "  mv s3, a3                   # value\n" ++
  "  mv s4, a4                   # value len\n" ++
  "  mv s5, a5                   # out\n" ++
  "  mv s6, a6                   # out len\n" ++
  "  # field 2 = storageRoot -> aps_off / aps_len\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 2; la a3, aps_off; la a4, aps_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Laps_parsefail\n" ++
  "  la t0, aps_len; ld t1, 0(t0); li t2, 32; bne t1, t2, .Laps_conservative\n" ++
  "  # compare the 32 storageRoot bytes (account + aps_off) to EMPTY_TRIE_ROOT\n" ++
  "  la t0, aps_off; ld t1, 0(t0); add t1, s0, t1   # storageRoot ptr\n" ++
  "  la t2, aps_empty_root; li t3, 32\n" ++
  ".Laps_cmp:\n" ++
  "  beqz t3, .Laps_empty\n" ++
  "  lbu t4, 0(t1); lbu t5, 0(t2); bne t4, t5, .Laps_conservative\n" ++
  "  addi t1, t1, 1; addi t2, t2, 1; addi t3, t3, -1; j .Laps_cmp\n" ++
  ".Laps_empty:\n" ++
  "  # new_storage_root = storage_root_single_slot(slot_key, value, value_len)\n" ++
  "  mv a0, s2; mv a1, s3; mv a2, s4; la a3, aps_newsroot\n" ++
  "  jal ra, storage_root_single_slot\n" ++
  "  # new account = account_set_storage_root(account, len, new_storage_root, out, out_len)\n" ++
  "  mv a0, s0; mv a1, s1; la a2, aps_newsroot; mv a3, s5; mv a4, s6\n" ++
  "  jal ra, account_set_storage_root\n" ++
  "  bnez a0, .Laps_parsefail\n" ++
  "  li a0, 0\n" ++
  "  j .Laps_ret\n" ++
  ".Laps_conservative:\n" ++
  "  li a0, 1\n" ++
  "  j .Laps_ret\n" ++
  ".Laps_parsefail:\n" ++
  "  li a0, 2\n" ++
  ".Laps_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"


/-! ## account_apply_storage_slot_acc
    Same external ABI as `account_apply_storage_slot`, but handles non-empty
    prior storage roots by updating the storage trie through `mpt_set_acc`.
    The caller must set `aps_witness_ptr` / `aps_witness_len` to the witness
    section containing the storage trie nodes before calling this helper. -/
def accountApplyStorageSlotAccFunction : String :=
  "account_apply_storage_slot_acc:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a0                   # account\n" ++
  "  mv s1, a1                   # account len\n" ++
  "  mv s2, a2                   # slot_key\n" ++
  "  mv s3, a3                   # value\n" ++
  "  mv s4, a4                   # value len\n" ++
  "  mv s5, a5                   # out\n" ++
  "  mv s6, a6                   # out len\n" ++
  "  # field 2 = storageRoot -> aps_off / aps_len\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 2; la a3, aps_off; la a4, aps_len\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lapsa_parsefail\n" ++
  "  la t0, aps_len; ld t1, 0(t0); li t2, 32; bne t1, t2, .Lapsa_conservative\n" ++
  "  la t0, aps_off; ld t1, 0(t0); add t1, s0, t1   # storageRoot ptr\n" ++
  "  la t2, aps_empty_root; li t3, 32\n" ++
  ".Lapsa_cmp:\n" ++
  "  beqz t3, .Lapsa_empty\n" ++
  "  lbu t4, 0(t1); lbu t5, 0(t2); bne t4, t5, .Lapsa_nonempty\n" ++
  "  addi t1, t1, 1; addi t2, t2, 1; addi t3, t3, -1; j .Lapsa_cmp\n" ++
  ".Lapsa_empty:\n" ++
  "  beqz s4, .Lapsa_copy_current\n" ++
  "  mv a0, s2; mv a1, s3; mv a2, s4; la a3, aps_newsroot\n" ++
  "  jal ra, storage_root_single_slot\n" ++
  "  j .Lapsa_set_account\n" ++
  ".Lapsa_nonempty:\n" ++
  "  # Need caller-provided witness for the existing storage trie.\n" ++
  "  la t0, aps_witness_ptr; ld t0, 0(t0); beqz t0, .Lapsa_conservative\n" ++
  "  beqz s4, .Lapsa_delete_nonempty\n" ++
  "  # RLP(value) is the leaf value stored in the storage trie.\n" ++
  "  mv a0, s3; mv a1, s4; la a2, srss_rlpval; la a3, srss_rlpval_len\n" ++
  "  jal ra, rlp_encode_bytes\n" ++
  "  # Storage path = nibbles(keccak256(slot_key)).\n" ++
  "  mv a0, s2; li a1, 32; la a2, srss_key\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  la a0, srss_key; li a1, 32; la a2, aps_path\n" ++
  "  jal ra, bytes_to_nibbles\n" ++
  "  # Update the non-empty storage trie through mpt_set_acc.\n" ++
  "  la t0, mset_db_count; sd zero, 0(t0)\n" ++
  "  la t0, mset_db_data; la t1, mset_db_top; sd t0, 0(t1)\n" ++
  "  la t0, aps_off; ld t0, 0(t0); add a0, s0, t0\n" ++
  "  la t0, aps_witness_ptr; ld a1, 0(t0)\n" ++
  "  la t0, aps_witness_len; ld a2, 0(t0)\n" ++
  "  la a3, aps_path; li a4, 64\n" ++
  "  la a5, srss_rlpval; la t0, srss_rlpval_len; ld a6, 0(t0); la a7, aps_newsroot\n" ++
  "  jal ra, mpt_set_acc\n" ++
  "  beqz a0, .Lapsa_set_account\n" ++
  "  # If the slot was absent, insert it into the existing storage trie.\n" ++
  "  la t0, mset_db_count; sd zero, 0(t0)\n" ++
  "  la t0, mset_db_data; la t1, mset_db_top; sd t0, 0(t1)\n" ++
  "  la t0, aps_off; ld t0, 0(t0); add a0, s0, t0\n" ++
  "  la t0, aps_witness_ptr; ld a1, 0(t0)\n" ++
  "  la t0, aps_witness_len; ld a2, 0(t0)\n" ++
  "  la a3, aps_path; li a4, 64\n" ++
  "  la a5, srss_rlpval; la t0, srss_rlpval_len; ld a6, 0(t0); la a7, aps_newsroot\n" ++
  "  jal ra, mpt_insert_acc\n" ++
  "  bnez a0, .Lapsa_conservative\n" ++
  ".Lapsa_set_account:\n" ++
  "  mv a0, s0; mv a1, s1; la a2, aps_newsroot; mv a3, s5; mv a4, s6\n" ++
  "  jal ra, account_set_storage_root\n" ++
  "  bnez a0, .Lapsa_parsefail\n" ++
  "  li a0, 0\n" ++
  "  j .Lapsa_ret\n" ++
  ".Lapsa_delete_nonempty:\n" ++
  "  mv a0, s2; li a1, 32; la a2, srss_key\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  la a0, srss_key; li a1, 32; la a2, aps_path\n" ++
  "  jal ra, bytes_to_nibbles\n" ++
  "  la t0, mset_db_count; sd zero, 0(t0)\n" ++
  "  la t0, mset_db_data; la t1, mset_db_top; sd t0, 0(t1)\n" ++
  "  la t0, aps_off; ld t0, 0(t0); add a0, s0, t0\n" ++
  "  la t0, aps_witness_ptr; ld a1, 0(t0)\n" ++
  "  la t0, aps_witness_len; ld a2, 0(t0)\n" ++
  "  la a3, aps_path; li a4, 64; la a7, aps_newsroot\n" ++
  "  jal ra, mpt_delete_acc\n" ++
  "  beqz a0, .Lapsa_set_account\n" ++
  "  j .Lapsa_conservative\n" ++
  ".Lapsa_copy_current:\n" ++
  "  mv a0, s5; mv a1, s0; mv a2, s1\n" ++
  "  jal ra, mset_memcpy\n" ++
  "  sd s1, 0(s6)\n" ++
  "  li a0, 0\n" ++
  "  j .Lapsa_ret\n" ++
  ".Lapsa_conservative:\n" ++
  "  li a0, 1\n" ++
  "  j .Lapsa_ret\n" ++
  ".Lapsa_parsefail:\n" ++
  "  li a0, 2\n" ++
  ".Lapsa_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-! ### zisk_account_apply_storage_slot probe.
    Input (file -> INPUT+8): file[0:8]=account_len, file[8:16]=value_len,
      file[16:48]=slot_key(32B), file[48:80]=value(<=32B), file[128:]=account RLP.
    Output: OUTPUT+0=status, OUTPUT+8=out_len, OUTPUT+16=new account RLP. -/
def ziskAccountApplyStorageSlotPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t0, 0x40000000\n" ++
  "  ld a1, 8(t0)                # account_len\n" ++
  "  ld a4, 16(t0)               # value_len\n" ++
  "  addi a2, t0, 24             # slot_key\n" ++
  "  addi a3, t0, 56             # value\n" ++
  "  addi a0, t0, 136            # account RLP\n" ++
  "  la a5, aps_out; la a6, aps_out_len\n" ++
  "  jal ra, account_apply_storage_slot\n" ++
  "  li t0, 0xa0010000; sd a0, 0(t0)\n" ++
  "  la t1, aps_out_len; ld t2, 0(t1); sd t2, 8(t0)\n" ++
  "  la t1, aps_out; addi t0, t0, 16; li t3, 0\n" ++
  ".Lapsp_cp:\n" ++
  "  beq t3, t2, .Lapsp_done\n" ++
  "  add t4, t1, t3; lbu t5, 0(t4); add t6, t0, t3; sb t5, 0(t6)\n" ++
  "  addi t3, t3, 1; j .Lapsp_cp\n" ++
  ".Lapsp_done:\n" ++
  "  j .Laps_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  bytesToNibblesFunction ++ "\n" ++
  hpEncodeNibblesFunction ++ "\n" ++
  rlpEncodeBytesFunction ++ "\n" ++
  rlpEncodeListPrefixFunction ++ "\n" ++
  singleLeafTrieRootFunction ++ "\n" ++
  storageRootSingleSlotFunction ++ "\n" ++
  msetMemcpyFunction ++ "\n" ++
  rlpItemSizeFunction ++ "\n" ++
  rlpItemSpanFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  mptSpliceSlotFunction ++ "\n" ++
  accountSetStorageRootFunction ++ "\n" ++
  accountApplyStorageSlotFunction ++ "\n" ++
  ".Laps_pdone:"

def ziskAccountApplyStorageSlotDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n  .zero 200\n" ++
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
  ".balign 8\n" ++
  "asr_ref:\n  .zero 40\n" ++
  "mset_span_start:\n  .zero 8\n" ++
  "mset_span_size:\n  .zero 8\n" ++
  "mset_payload_start:\n  .zero 8\n" ++
  "mset_head_len:\n  .zero 8\n" ++
  "mset_tail_start:\n  .zero 8\n" ++
  "mset_tail_len:\n  .zero 8\n" ++
  "mset_new_payload_len:\n  .zero 8\n" ++
  "mset_prefix_len:\n  .zero 8\n" ++
  "mset_cursor:\n  .zero 8\n" ++
  ".balign 8\n" ++
  "aps_off:\n  .zero 8\n" ++
  "aps_len:\n  .zero 8\n" ++
  "aps_out_len:\n  .zero 8\n" ++
  "aps_witness_ptr:\n  .zero 8\n" ++
  "aps_witness_len:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "aps_newsroot:\n  .zero 32\n" ++
  "aps_path:\n  .zero 64\n" ++
  "aps_empty_root:\n" ++
  "  .byte 0x56, 0xe8, 0x1f, 0x17, 0x1b, 0xcc, 0x55, 0xa6\n" ++
  "  .byte 0xff, 0x83, 0x45, 0xe6, 0x92, 0xc0, 0xf8, 0x6e\n" ++
  "  .byte 0x5b, 0x48, 0xe0, 0x1b, 0x99, 0x6c, 0xad, 0xc0\n" ++
  "  .byte 0x01, 0x62, 0x2f, 0xb5, 0xe3, 0x63, 0xb4, 0x21\n" ++
  ".balign 8\n" ++
  "aps_out:\n  .zero 256"

def ziskAccountApplyStorageSlotProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskAccountApplyStorageSlotPrologue
  dataAsm     := ziskAccountApplyStorageSlotDataSection
}

end EvmAsm.Codegen
