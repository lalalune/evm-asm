/-
  EvmAsm.Codegen.Programs.MptSet

  MPT post-state-root recompute (bead evm-asm-fhsxz.4): the value-only
  update of an EXISTING key, in two pieces —

    .4.2.1  record-walk    (THIS file, first piece): descend the trie
            exactly like `mpt_walk`, but instead of extracting the value,
            emit the *descent node-stack* (root .. leaf) so the caller can
            re-encode the touched nodes bottom-up.
    .4.2.2  bubble-up       (follow-up): consume the node-stack, re-encode
            the leaf with the new value, then walk back up re-encoding each
            parent's touched slot, hashing as we go, to obtain the new root.

  `mpt_set_record_walk` forks `mpt_walk` (Programs/Mpt.lean): same node-kind
  dispatch, same inline-vs-32-byte-hash child deref, same HP-path compare.
  The only additions are: (a) before descending through a BRANCH or
  EXTENSION, push a 32-byte record to `stack_out`; (b) at the LEAF, write a
  32-byte `meta_out` block instead of copying the value.

  All multi-byte memory accesses are naturally aligned (the project's
  no-misaligned invariant): the records and meta are u64-granular stores to
  8-aligned output cursors; node bodies are read via the same byte-wise
  helpers `mpt_walk` already uses.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.Mpt

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## mpt_set_record_walk -- record the descent path of an MPT lookup

    Identical descent to `mpt_walk`, but the output is the *node stack*
    along the root→leaf path (so a later bubble-up pass can re-encode the
    touched nodes) rather than the matched value.

    Calling convention:
      a0 (input)  : root_hash ptr (32 bytes)
      a1 (input)  : witness section ptr
      a2 (input)  : witness section_len
      a3 (input)  : path_nibbles ptr (one byte per nibble)
      a4 (input)  : path_nibbles_len
      a5 (input)  : stack_out ptr (32 bytes per descended node)
      a6 (input)  : meta_out ptr (32 bytes)
      ra (input)  : return
      a0 (output) : 0 (found) / 1 (not found) / 2 (parse error)

    `stack_out` entry layout (32 bytes, one per BRANCH/EXTENSION descended,
    in root→leaf order):
      +0  node_offset : u64  byte offset of this node's RLP within the
                             witness section (= node_ptr - witness_ptr)
      +8  node_len    : u64  full RLP length of this node
      +16 kind        : u64  0 = branch, 1 = extension
      +24 nibble      : u64  branch: child index taken; extension: 0

    `meta_out` layout (32 bytes), written on a successful (found) walk:
      +0  depth           : u64  number of stack_out entries
      +8  consumed        : u64  path nibbles consumed by branches/extensions
                                 above the leaf (NOT incl. the leaf's HP path)
      +16 leaf_offset     : u64  byte offset of the terminal node's RLP
      +24 leaf_len        : u64  full RLP length of the terminal node

    Registers (callee-saved, mirrors mpt_walk + s9 for depth):
      s0 witness ptr   s1 witness_len   s2 path ptr   s3 path_len
      s4 stack_out cursor   s5 meta_out ptr
      s6 consumed nibbles   s7 current node ptr   s8 current node len
      s9 depth (records pushed)

    Reuses mpt_walk's scratch labels (mw_lookup_hash, mw_*_offset/length,
    mw_nibble_buf, ...) from `ziskMptWalkDataSection`. -/
def mptSetRecordWalkFunction : String :=
  "mpt_set_record_walk:\n" ++
  "  addi sp, sp, -96\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  sd s8, 72(sp); sd s9, 80(sp)\n" ++
  "  mv s0, a1                   # s0 = witness ptr\n" ++
  "  mv s1, a2                   # s1 = witness_len\n" ++
  "  mv s2, a3                   # s2 = path_nibbles ptr\n" ++
  "  mv s3, a4                   # s3 = path_nibbles_len\n" ++
  "  mv s4, a5                   # s4 = stack_out cursor\n" ++
  "  mv s5, a6                   # s5 = meta_out ptr\n" ++
  "  li s9, 0                    # s9 = depth\n" ++
  "  # Copy root_hash to mw_lookup_hash for the first lookup.\n" ++
  "  la t0, mw_lookup_hash\n" ++
  "  ld t1,  0(a0); sd t1,  0(t0)\n" ++
  "  ld t1,  8(a0); sd t1,  8(t0)\n" ++
  "  ld t1, 16(a0); sd t1, 16(t0)\n" ++
  "  ld t1, 24(a0); sd t1, 24(t0)\n" ++
  "  # First lookup of root_hash in witness.\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s1\n" ++
  "  la a2, mw_lookup_hash\n" ++
  "  la a3, mw_lookup_offset\n" ++
  "  la a4, mw_lookup_length\n" ++
  "  jal ra, witness_lookup_by_hash\n" ++
  "  bnez a0, .Lmsrw_not_found\n" ++
  "  la t0, mw_lookup_offset; ld t1, 0(t0); add s7, s0, t1\n" ++
  "  la t0, mw_lookup_length; ld s8, 0(t0)\n" ++
  "  li s6, 0\n" ++
  ".Lmsrw_loop:\n" ++
  "  mv a0, s7\n" ++
  "  mv a1, s8\n" ++
  "  jal ra, mpt_node_kind\n" ++
  "  beqz a0, .Lmsrw_branch\n" ++
  "  li t0, 1; beq a0, t0, .Lmsrw_extension\n" ++
  "  li t0, 2; beq a0, t0, .Lmsrw_leaf\n" ++
  "  j .Lmsrw_parse_fail\n" ++
  ".Lmsrw_branch:\n" ++
  "  beq s6, s3, .Lmsrw_branch_end\n" ++
  "  add t0, s2, s6              # &path[consumed]\n" ++
  "  lbu t1, 0(t0)               # nibble (item index)\n" ++
  "  # push record (node_offset, node_len, kind=0 branch, nibble)\n" ++
  "  sub t2, s7, s0              # node_offset within witness\n" ++
  "  sd t2,  0(s4)\n" ++
  "  sd s8,  8(s4)\n" ++
  "  sd zero, 16(s4)            # kind = 0 (branch)\n" ++
  "  sd t1, 24(s4)\n" ++
  "  addi s4, s4, 32\n" ++
  "  addi s9, s9, 1\n" ++
  "  # descend into child slot via rlp_list_nth_item.\n" ++
  "  mv a0, s7\n" ++
  "  mv a1, s8\n" ++
  "  mv a2, t1                   # nibble\n" ++
  "  la a3, mw_child_offset\n" ++
  "  la a4, mw_child_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  addi s6, s6, 1\n" ++
  "  bnez a0, .Lmsrw_parse_fail\n" ++
  "  la t0, mw_child_length; ld t1, 0(t0)\n" ++
  "  beqz t1, .Lmsrw_not_found   # empty slot\n" ++
  "  li t2, 32\n" ++
  "  beq t1, t2, .Lmsrw_branch_hash\n" ++
  "  # Inlined (length 1..31): node = (s7 + child_offset, child_length).\n" ++
  "  la t0, mw_child_offset; ld t2, 0(t0)\n" ++
  "  add s7, s7, t2\n" ++
  "  mv s8, t1\n" ++
  "  j .Lmsrw_loop\n" ++
  ".Lmsrw_branch_hash:\n" ++
  "  # 32-byte hash: copy to mw_lookup_hash then lookup.\n" ++
  "  la t0, mw_child_offset; ld t1, 0(t0)\n" ++
  "  add t2, s7, t1\n" ++
  "  la t3, mw_lookup_hash\n" ++
  "  ld t4,  0(t2); sd t4,  0(t3)\n" ++
  "  ld t4,  8(t2); sd t4,  8(t3)\n" ++
  "  ld t4, 16(t2); sd t4, 16(t3)\n" ++
  "  ld t4, 24(t2); sd t4, 24(t3)\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s1\n" ++
  "  la a2, mw_lookup_hash\n" ++
  "  la a3, mw_lookup_offset\n" ++
  "  la a4, mw_lookup_length\n" ++
  "  jal ra, witness_lookup_by_hash\n" ++
  "  bnez a0, .Lmsrw_not_found\n" ++
  "  la t0, mw_lookup_offset; ld t1, 0(t0); add s7, s0, t1\n" ++
  "  la t0, mw_lookup_length; ld s8, 0(t0)\n" ++
  "  j .Lmsrw_loop\n" ++
  ".Lmsrw_branch_end:\n" ++
  "  # Path exhausted at a branch: this branch is the terminal node\n" ++
  "  # (value lives in slot 16). Record it as the terminal in meta.\n" ++
  "  sd s9, 0(s5)               # depth\n" ++
  "  sd s6, 8(s5)               # consumed\n" ++
  "  sub t0, s7, s0; sd t0, 16(s5) # leaf_offset\n" ++
  "  sd s8, 24(s5)              # leaf_len\n" ++
  "  li a0, 0\n" ++
  "  j .Lmsrw_ret\n" ++
  ".Lmsrw_extension:\n" ++
  "  mv a0, s7\n" ++
  "  mv a1, s8\n" ++
  "  li a2, 0\n" ++
  "  la a3, mw_path_offset\n" ++
  "  la a4, mw_path_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lmsrw_parse_fail\n" ++
  "  la t0, mw_path_offset; ld t1, 0(t0); add a0, s7, t1\n" ++
  "  la t0, mw_path_length; ld a1, 0(t0)\n" ++
  "  la a2, mw_nibble_buf\n" ++
  "  la a3, mw_nibble_count\n" ++
  "  la a4, mw_is_leaf\n" ++
  "  jal ra, hp_decode_nibbles\n" ++
  "  bnez a0, .Lmsrw_parse_fail\n" ++
  "  la t0, mw_is_leaf; ld t1, 0(t0)\n" ++
  "  bnez t1, .Lmsrw_parse_fail  # node kind said extension; HP says leaf\n" ++
  "  la t0, mw_nibble_count; ld t1, 0(t0)\n" ++
  "  add t2, s6, t1\n" ++
  "  bgtu t2, s3, .Lmsrw_not_found\n" ++
  "  # Compare extension nibbles against path[consumed..].\n" ++
  "  la t2, mw_nibble_buf\n" ++
  "  add t3, s2, s6\n" ++
  "  mv t4, t1\n" ++
  ".Lmsrw_ext_cmp:\n" ++
  "  beqz t4, .Lmsrw_ext_cmp_done\n" ++
  "  lbu t5, 0(t2)\n" ++
  "  lbu t6, 0(t3)\n" ++
  "  bne t5, t6, .Lmsrw_not_found\n" ++
  "  addi t2, t2, 1\n" ++
  "  addi t3, t3, 1\n" ++
  "  addi t4, t4, -1\n" ++
  "  j .Lmsrw_ext_cmp\n" ++
  ".Lmsrw_ext_cmp_done:\n" ++
  "  add s6, s6, t1\n" ++
  "  # push record (node_offset, node_len, kind=1 extension, nibble=0)\n" ++
  "  sub t2, s7, s0\n" ++
  "  sd t2,  0(s4)\n" ++
  "  sd s8,  8(s4)\n" ++
  "  li t3, 1; sd t3, 16(s4)    # kind = 1 (extension)\n" ++
  "  sd zero, 24(s4)\n" ++
  "  addi s4, s4, 32\n" ++
  "  addi s9, s9, 1\n" ++
  "  # Get item 1 (child ref).\n" ++
  "  mv a0, s7\n" ++
  "  mv a1, s8\n" ++
  "  li a2, 1\n" ++
  "  la a3, mw_child_offset\n" ++
  "  la a4, mw_child_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lmsrw_parse_fail\n" ++
  "  la t0, mw_child_length; ld t1, 0(t0)\n" ++
  "  la t0, mw_child_offset; ld t2, 0(t0)\n" ++
  "  add t3, s7, t2\n" ++
  "  li t4, 32\n" ++
  "  beq t1, t4, .Lmsrw_ext_hash\n" ++
  "  # Inline child: t3 is its ptr, t1 is its length.\n" ++
  "  mv s7, t3\n" ++
  "  mv s8, t1\n" ++
  "  j .Lmsrw_loop\n" ++
  ".Lmsrw_ext_hash:\n" ++
  "  la t4, mw_lookup_hash\n" ++
  "  ld t5,  0(t3); sd t5,  0(t4)\n" ++
  "  ld t5,  8(t3); sd t5,  8(t4)\n" ++
  "  ld t5, 16(t3); sd t5, 16(t4)\n" ++
  "  ld t5, 24(t3); sd t5, 24(t4)\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s1\n" ++
  "  la a2, mw_lookup_hash\n" ++
  "  la a3, mw_lookup_offset\n" ++
  "  la a4, mw_lookup_length\n" ++
  "  jal ra, witness_lookup_by_hash\n" ++
  "  bnez a0, .Lmsrw_not_found\n" ++
  "  la t0, mw_lookup_offset; ld t1, 0(t0); add s7, s0, t1\n" ++
  "  la t0, mw_lookup_length; ld s8, 0(t0)\n" ++
  "  j .Lmsrw_loop\n" ++
  ".Lmsrw_leaf:\n" ++
  "  mv a0, s7\n" ++
  "  mv a1, s8\n" ++
  "  li a2, 0\n" ++
  "  la a3, mw_path_offset\n" ++
  "  la a4, mw_path_length\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lmsrw_parse_fail\n" ++
  "  la t0, mw_path_offset; ld t1, 0(t0); add a0, s7, t1\n" ++
  "  la t0, mw_path_length; ld a1, 0(t0)\n" ++
  "  la a2, mw_nibble_buf\n" ++
  "  la a3, mw_nibble_count\n" ++
  "  la a4, mw_is_leaf\n" ++
  "  jal ra, hp_decode_nibbles\n" ++
  "  bnez a0, .Lmsrw_parse_fail\n" ++
  "  la t0, mw_is_leaf; ld t1, 0(t0)\n" ++
  "  li t2, 1\n" ++
  "  bne t1, t2, .Lmsrw_parse_fail\n" ++
  "  la t0, mw_nibble_count; ld t1, 0(t0)\n" ++
  "  sub t2, s3, s6              # remaining nibbles\n" ++
  "  bne t1, t2, .Lmsrw_not_found\n" ++
  "  la t2, mw_nibble_buf\n" ++
  "  add t3, s2, s6\n" ++
  "  mv t4, t1\n" ++
  ".Lmsrw_leaf_cmp:\n" ++
  "  beqz t4, .Lmsrw_leaf_match\n" ++
  "  lbu t5, 0(t2)\n" ++
  "  lbu t6, 0(t3)\n" ++
  "  bne t5, t6, .Lmsrw_not_found\n" ++
  "  addi t2, t2, 1\n" ++
  "  addi t3, t3, 1\n" ++
  "  addi t4, t4, -1\n" ++
  "  j .Lmsrw_leaf_cmp\n" ++
  ".Lmsrw_leaf_match:\n" ++
  "  sd s9, 0(s5)               # depth\n" ++
  "  sd s6, 8(s5)               # consumed\n" ++
  "  sub t0, s7, s0; sd t0, 16(s5) # leaf_offset\n" ++
  "  sd s8, 24(s5)              # leaf_len\n" ++
  "  li a0, 0\n" ++
  "  j .Lmsrw_ret\n" ++
  ".Lmsrw_not_found:\n" ++
  "  li a0, 1\n" ++
  "  j .Lmsrw_ret\n" ++
  ".Lmsrw_parse_fail:\n" ++
  "  li a0, 2\n" ++
  ".Lmsrw_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp); ld s9, 80(sp)\n" ++
  "  addi sp, sp, 96\n" ++
  "  ret"

/-- `zisk_mpt_set_record_walk`: probe BuildUnit. Reuses the `mpt_set` probe
    input layout (scripts/mpt_ref.py `build_probe_input`): the new_value
    field is present but ignored by the record-walk.
    Input layout (file maps to INPUT+8 at 0x40000000):
      INPUT+8  : witness_len (u64)
      INPUT+16 : path_len (u64)
      INPUT+24 : new_value_len (u64)         [ignored here]
      INPUT+32 : root_hash (32 bytes)
      INPUT+64 : path_nibbles (1B each)
      INPUT+64+path_len : new_value
      8-aligned : witness section
    Output layout:
      OUTPUT+0   : status (0 found / 1 not / 2 fail)
      OUTPUT+8   : meta (depth, consumed, leaf_offset, leaf_len) -- 32 B
      OUTPUT+128 : stack records, 32 B each (node_offset, node_len, kind,
                   nibble), in root->leaf order -/
def ziskMptSetRecordWalkPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a7, 0x40000000\n" ++
  "  ld t6, 8(a7)                # witness_len\n" ++
  "  ld t5, 16(a7)               # path_len\n" ++
  "  ld t4, 24(a7)               # new_value_len\n" ++
  "  addi a0, a7, 32             # root_hash ptr (INPUT+32)\n" ++
  "  addi a3, a7, 64             # path_nibbles ptr (INPUT+64)\n" ++
  "  # witness ptr = path_ptr + roundup8(path_len + new_value_len).\n" ++
  "  add t3, t5, t4\n" ++
  "  addi t3, t3, 7\n" ++
  "  andi t3, t3, -8\n" ++
  "  add a1, a3, t3              # witness ptr\n" ++
  "  mv a2, t6                   # witness_len\n" ++
  "  mv a4, t5                   # path_len\n" ++
  "  li a5, 0xa0010080           # stack_out at OUTPUT + 128\n" ++
  "  li a6, 0xa0010008           # meta_out at OUTPUT + 8\n" ++
  "  jal ra, mpt_set_record_walk\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status at OUTPUT + 0\n" ++
  "  j .Lmsrw_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  witnessLookupByHashFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  mptNodeKindFunction ++ "\n" ++
  hpDecodeNibblesFunction ++ "\n" ++
  mptSetRecordWalkFunction ++ "\n" ++
  ".Lmsrw_pdone:"

def ziskMptSetRecordWalkProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskMptSetRecordWalkPrologue
  dataAsm     := ziskMptWalkDataSection
}

end EvmAsm.Codegen
