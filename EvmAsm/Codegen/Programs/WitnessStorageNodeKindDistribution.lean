/-
  EvmAsm.Codegen.Programs.WitnessStorageNodeKindDistribution

  Storage-side mirror of #7207
  (`witness_state_node_kind_distribution`). Iterates the
  witness.storage SSZ list section, classifies each entry
  via K22 mpt_node_kind, and returns per-kind counts in a
  32-byte buffer.

  Function body is structurally identical to the state-side
  primitive (both operate over SSZ List[Bytes] sections of
  MPT nodes). Distinct primitive exists for the same
  reasons as #7260: separate ELF, separate fixtures, and
  intent-revealing name at call sites.

  No proofs yet -- codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.Mpt
import EvmAsm.Codegen.Programs.HashBridge

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## witness_storage_node_kind_distribution

    Iterate every element of a witness.storage SSZ list
    section, call K22 mpt_node_kind on each, and accumulate
    counts of {branch, extension, leaf, parse_fail} into a
    32-byte output buffer (4 × u64 LE).

    Storage-side mirror of #7207. Useful storage-specific
    sanity checks:
      * A "single populated slot" storage trie has exactly
        ONE leaf and zero branches/extensions. Counts that
        deviate are bugged.
      * A populated multi-slot trie of N slots has
        leaf_count ≥ N (each leaf node carries the slot
        value) -- though some leaves may be embedded in
        branches' value slot, in which case the witness
        wouldn't list them separately.
      * A section dominated by parse_fail entries is
        broken.

    Output layout (32 bytes):
      bytes  0.. 8 : count_branch    (K22 = 0)
      bytes  8..16 : count_extension (K22 = 1)
      bytes 16..24 : count_leaf      (K22 = 2)
      bytes 24..32 : count_parse_fail (K22 = 3)

    Calling convention (3 args):
      a0 (input)  : witness.storage ptr
      a1 (input)  : witness.storage len
      a2 (input)  : output buffer ptr (32 bytes)
      ra (input)  : return

      a0 (output) : 0 (always; K22 parse failures counted
                    into slot 3, not propagated)
-/
def witnessStorageNodeKindDistributionFunction : String :=
  "witness_storage_node_kind_distribution:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a0                  # section ptr\n" ++
  "  mv s1, a1                  # section_len\n" ++
  "  mv s2, a2                  # out buffer ptr\n" ++
  "  sd zero,  0(s2); sd zero,  8(s2); sd zero, 16(s2); sd zero, 24(s2)\n" ++
  "  beqz s1, .Lwznd_done\n" ++
  "  lwu t0, 0(s0)\n" ++
  "  srli s3, t0, 2             # s3 = N\n" ++
  "  li s4, 0                   # s4 = i\n" ++
  ".Lwznd_loop:\n" ++
  "  beq s4, s3, .Lwznd_done\n" ++
  "  slli t0, s4, 2\n" ++
  "  add t1, s0, t0\n" ++
  "  lwu t2, 0(t1)\n" ++
  "  add s5, s0, t2             # el_i_start\n" ++
  "  addi t3, s4, 1\n" ++
  "  beq t3, s3, .Lwznd_use_end\n" ++
  "  slli t3, t3, 2\n" ++
  "  add t3, s0, t3\n" ++
  "  lwu t4, 0(t3)\n" ++
  "  add t4, s0, t4             # el_i_end\n" ++
  "  j .Lwznd_have_end\n" ++
  ".Lwznd_use_end:\n" ++
  "  add t4, s0, s1\n" ++
  ".Lwznd_have_end:\n" ++
  "  sub s6, t4, s5             # el_i_len\n" ++
  "  mv a0, s5\n" ++
  "  mv a1, s6\n" ++
  "  jal ra, mpt_node_kind\n" ++
  "  slli t0, a0, 3\n" ++
  "  add t1, s2, t0\n" ++
  "  ld t2, 0(t1)\n" ++
  "  addi t2, t2, 1\n" ++
  "  sd t2, 0(t1)\n" ++
  "  addi s4, s4, 1\n" ++
  "  j .Lwznd_loop\n" ++
  ".Lwznd_done:\n" ++
  "  li a0, 0\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-- `zisk_witness_storage_node_kind_distribution`: probe BuildUnit.
    Input layout (at INPUT_ADDR):
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : witness_storage_len (u64 LE)
      bytes 16..   : witness.storage section bytes
    Output layout (40 bytes):
      bytes  0.. 8 : status (always 0)
      bytes  8..16 : count_branch
      bytes 16..24 : count_extension
      bytes 24..32 : count_leaf
      bytes 32..40 : count_parse_fail -/
def ziskWitnessStorageNodeKindDistributionPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a6, 0x40000000\n" ++
  "  ld a1, 8(a6)                # witness_storage_len\n" ++
  "  addi a0, a6, 16             # witness.storage ptr\n" ++
  "  li a2, 0xa0010008           # out buffer ptr (32 B)\n" ++
  "  jal ra, witness_storage_node_kind_distribution\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lwznd_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  mptNodeKindFunction ++ "\n" ++
  witnessStorageNodeKindDistributionFunction ++ "\n" ++
  ".Lwznd_pdone:"

def ziskWitnessStorageNodeKindDistributionDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "mnk_dummy_offset:\n" ++
  "  .zero 8\n" ++
  "mnk_dummy_length:\n" ++
  "  .zero 8\n" ++
  "mnk_path_offset:\n" ++
  "  .zero 8\n" ++
  "mnk_path_length:\n" ++
  "  .zero 8"

def ziskWitnessStorageNodeKindDistributionProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskWitnessStorageNodeKindDistributionPrologue
  dataAsm     := ziskWitnessStorageNodeKindDistributionDataSection
}

end EvmAsm.Codegen
