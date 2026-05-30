/-
  EvmAsm.Codegen.Programs.WitnessStateKeccakAtIndex

  Index-based keccak256 reader over a witness.state SSZ
  list section. Given the section and an index, return the
  32-byte keccak256 hash of the entry at that index.

  Counterpart to K19 `witness_lookup_by_hash` which goes the
  other direction (hash -> offset). This primitive goes
  index -> hash, useful when a caller is iterating the
  witness in order rather than dispatching by hash.

  No proofs yet -- codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.HashBridge

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## witness_state_keccak_at_index

    Read the i-th entry of a witness.state SSZ list section
    (or any SSZ List[Bytes]) and return its keccak256 hash
    in a 32-byte output buffer.

    Why this exists alongside K19:
      * K19 (`witness_lookup_by_hash`) is hash -> entry: you
        already have the target hash and want to find which
        entry it is.
      * THIS primitive is index -> hash: you want to walk
        the witness in order (e.g. for auditing or for
        verifying a producer's claimed entry-hash list).

    Use cases:
      * Test/fixture introspection: "what's keccak of the
        3rd entry in this witness?"
      * Manual MPT-walk: caller maintains the (cursor_hash,
        path_remaining) walk state and uses this primitive
        to materialise the next node hash from the index
        they already have.
      * Producer-claim verification: the caller has a list
        of N expected entry hashes (from off-chain
        bookkeeping) and wants to verify them in order.

    Calling convention (4 args):
      a0 (input)  : witness.state ptr
      a1 (input)  : witness.state len
      a2 (input)  : index (u64)
      a3 (input)  : 32-byte out buffer ptr
      ra (input)  : return

      a0 (output) :
        0 = success (32 bytes of keccak hash written)
        1 = index out of bounds (or empty section)
        (no other failure modes; SSZ structural problems
        in the inner-offset table will silently produce
        wrong hashes but not propagate as errors --
        callers wanting validation should chain
        witness_state_node_kind_distribution first)
-/
def witnessStateKeccakAtIndexFunction : String :=
  "witness_state_keccak_at_index:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp)\n" ++
  "  mv s0, a0                  # section ptr\n" ++
  "  mv s1, a1                  # section_len\n" ++
  "  mv s2, a2                  # index\n" ++
  "  mv s3, a3                  # out buf ptr (32 B)\n" ++
  "  # Zero out_buf so OOB callers get a deterministic zero.\n" ++
  "  sd zero,  0(s3); sd zero,  8(s3)\n" ++
  "  sd zero, 16(s3); sd zero, 24(s3)\n" ++
  "  beqz s1, .Lwski_oob        # empty section ⇒ any index is OOB\n" ++
  "  lwu t0, 0(s0)              # first inner offset = 4 * N\n" ++
  "  srli s4, t0, 2             # s4 = N\n" ++
  "  bgeu s2, s4, .Lwski_oob    # index >= N ⇒ OOB\n" ++
  "  # Compute element i bounds.\n" ++
  "  slli t0, s2, 2             # 4*i\n" ++
  "  add t1, s0, t0\n" ++
  "  lwu t2, 0(t1)              # inner_off_i\n" ++
  "  add a0, s0, t2             # el_i_start\n" ++
  "  addi t3, s2, 1\n" ++
  "  beq t3, s4, .Lwski_use_end\n" ++
  "  slli t3, t3, 2\n" ++
  "  add t3, s0, t3\n" ++
  "  lwu t4, 0(t3)\n" ++
  "  add t4, s0, t4             # el_i_end\n" ++
  "  j .Lwski_have_end\n" ++
  ".Lwski_use_end:\n" ++
  "  add t4, s0, s1             # el_i_end = section_end\n" ++
  ".Lwski_have_end:\n" ++
  "  sub a1, t4, a0             # el_i_len\n" ++
  "  mv a2, s3                  # out buf\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  li a0, 0\n" ++
  "  j .Lwski_ret\n" ++
  ".Lwski_oob:\n" ++
  "  li a0, 1\n" ++
  ".Lwski_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- `zisk_witness_state_keccak_at_index`: probe BuildUnit.
    Input layout (at INPUT_ADDR):
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : witness_state_len (u64 LE)
      bytes 16..24 : index (u64 LE)
      bytes 24..   : witness.state section bytes
    Output layout (40 bytes):
      bytes  0.. 8 : status (0 = ok, 1 = OOB)
      bytes  8..40 : 32-byte keccak hash (zero on OOB) -/
def ziskWitnessStateKeccakAtIndexPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a6, 0x40000000\n" ++
  "  ld a1, 8(a6)                # witness_state_len\n" ++
  "  ld a2, 16(a6)               # index\n" ++
  "  addi a0, a6, 24             # witness.state ptr\n" ++
  "  li a3, 0xa0010008           # out buf ptr (32 B)\n" ++
  "  jal ra, witness_state_keccak_at_index\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lwski_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  witnessStateKeccakAtIndexFunction ++ "\n" ++
  ".Lwski_pdone:"

def ziskWitnessStateKeccakAtIndexDataSection : String :=
  ".section .data\n" ++
  ".balign 32\n" ++
  "zk3_state:\n" ++
  "  .zero 200"

def ziskWitnessStateKeccakAtIndexProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskWitnessStateKeccakAtIndexPrologue
  dataAsm     := ziskWitnessStateKeccakAtIndexDataSection
}

end EvmAsm.Codegen
