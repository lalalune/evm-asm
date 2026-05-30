/-
  EvmAsm.Codegen.Programs.WitnessNodeKindDistribution

  Witness auditing primitive: classify every entry in a
  witness.state SSZ list section using K22 `mpt_node_kind`,
  and return the per-kind counts. Distinct from the
  inclusion-proof family -- this doesn't hash anything,
  doesn't walk, doesn't compare. Just structural shape audit.

  Useful as a fail-fast malformed-witness detector before
  spending cycles on a full state walk.

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

/-! ## witness_state_node_kind_distribution

    Iterate every element of a witness.state SSZ list section,
    call K22 `mpt_node_kind` on each, and accumulate counts
    of {branch, extension, leaf, parse_fail} into a 32-byte
    output buffer (4 × u64 LE).

    Useful for:
      * Detecting malformed witnesses where the section is
        nonempty but contains zero parsable MPT nodes (often
        a sign of incorrect serialisation or wrong-section
        confusion -- e.g. a code section pasted in as state).
      * Pre-flight sanity checks: a multi-account state trie
        of depth d must contain at least one branch node
        (unless N=1 in which case a single leaf suffices).
      * Auditing witness bloat: a section dominated by
        parse_fail entries is broken; one dominated by leaves
        relative to branches may indicate a high fan-out
        without proper branch packing.

    Does NOT walk any links between nodes. Does NOT compute
    keccak hashes. Pure entry-wise classification.

    Calling convention (3 args):
      a0 (input)  : witness.state ptr
      a1 (input)  : witness.state len
      a2 (input)  : output buffer ptr (32 bytes)
      ra (input)  : return

      a0 (output) : 0 = success (always; K22 parse failures
                    are counted into slot 3, not propagated)

    Output buffer layout (32 bytes):
      bytes  0.. 8 : count_branch    (K22 return = 0)
      bytes  8..16 : count_extension (K22 return = 1)
      bytes 16..24 : count_leaf      (K22 return = 2)
      bytes 24..32 : count_parse_fail (K22 return = 3)

    Note: K22 distinguishes nodes via item-2 probe + HP-nibble
    inspection, NOT by absolute structural correctness. A
    section entry that has the right RLP shape but invalid
    semantic content (e.g. branch with wrong child-hash sizes)
    will still be classified as branch -- the validity
    surfaces during the actual walk.
-/
def witnessStateNodeKindDistributionFunction : String :=
  "witness_state_node_kind_distribution:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a0                  # section ptr\n" ++
  "  mv s1, a1                  # section_len\n" ++
  "  mv s2, a2                  # out buffer ptr\n" ++
  "  # Zero the 32-byte output buffer.\n" ++
  "  sd zero,  0(s2); sd zero,  8(s2); sd zero, 16(s2); sd zero, 24(s2)\n" ++
  "  beqz s1, .Lwsnd_done       # empty section -> all counts 0\n" ++
  "  # First inner offset (=4*N) gives N.\n" ++
  "  lwu t0, 0(s0)\n" ++
  "  srli s3, t0, 2             # s3 = N\n" ++
  "  li s4, 0                   # s4 = i = current index\n" ++
  ".Lwsnd_loop:\n" ++
  "  beq s4, s3, .Lwsnd_done\n" ++
  "  # Compute element i bounds.\n" ++
  "  slli t0, s4, 2             # 4*i\n" ++
  "  add t1, s0, t0\n" ++
  "  lwu t2, 0(t1)              # inner_off_i\n" ++
  "  add s5, s0, t2             # el_i_start  (preserve across K22 call)\n" ++
  "  addi t3, s4, 1\n" ++
  "  beq t3, s3, .Lwsnd_use_end\n" ++
  "  slli t3, t3, 2\n" ++
  "  add t3, s0, t3\n" ++
  "  lwu t4, 0(t3)\n" ++
  "  add t4, s0, t4             # el_i_end\n" ++
  "  j .Lwsnd_have_end\n" ++
  ".Lwsnd_use_end:\n" ++
  "  add t4, s0, s1             # el_i_end = section_end\n" ++
  ".Lwsnd_have_end:\n" ++
  "  sub s6, t4, s5             # el_i_len   (preserve across K22 call)\n" ++
  "  mv a0, s5\n" ++
  "  mv a1, s6\n" ++
  "  jal ra, mpt_node_kind\n" ++
  "  # a0 is 0/1/2/3 -- increment count[a0].\n" ++
  "  slli t0, a0, 3             # a0 * 8\n" ++
  "  add t1, s2, t0\n" ++
  "  ld t2, 0(t1)\n" ++
  "  addi t2, t2, 1\n" ++
  "  sd t2, 0(t1)\n" ++
  "  addi s4, s4, 1\n" ++
  "  j .Lwsnd_loop\n" ++
  ".Lwsnd_done:\n" ++
  "  li a0, 0\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-- `zisk_witness_state_node_kind_distribution`: probe BuildUnit.
    Input layout (at INPUT_ADDR):
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : witness_state_len (u64 LE)
      bytes 16..   : witness.state section bytes
    Output layout (40 bytes):
      bytes  0.. 8 : status (always 0)
      bytes  8..16 : count_branch
      bytes 16..24 : count_extension
      bytes 24..32 : count_leaf
      bytes 32..40 : count_parse_fail -/
def ziskWitnessStateNodeKindDistributionPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a6, 0x40000000\n" ++
  "  ld a1, 8(a6)                # witness_state_len\n" ++
  "  addi a0, a6, 16             # witness.state ptr\n" ++
  "  li a2, 0xa0010008           # out buffer ptr (32 B)\n" ++
  "  jal ra, witness_state_node_kind_distribution\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lwsnd_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  mptNodeKindFunction ++ "\n" ++
  witnessStateNodeKindDistributionFunction ++ "\n" ++
  ".Lwsnd_pdone:"

def ziskWitnessStateNodeKindDistributionDataSection : String :=
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

def ziskWitnessStateNodeKindDistributionProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskWitnessStateNodeKindDistributionPrologue
  dataAsm     := ziskWitnessStateNodeKindDistributionDataSection
}

end EvmAsm.Codegen
