/-
  EvmAsm.Codegen.Programs.WitnessStorageKeccakAtIndex

  Storage-side mirror of #7215
  (`witness_state_keccak_at_index`). Index-based keccak256
  reader over the `witness.storage` SSZ list section.

  The function body is structurally identical to the state-
  side primitive -- both operate over arbitrary `List[Bytes]`
  SSZ sections. The distinct primitive exists to give callers
  a name that matches the section they're auditing, and to
  document use cases specific to storage.

  No proofs yet -- codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.HashBridge

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## witness_storage_keccak_at_index

    Read the i-th entry of a witness.storage SSZ list
    section and return its keccak256 hash in a 32-byte
    output buffer.

    Storage-side mirror of #7215. The function body is the
    same as the state-side primitive; this primitive exists
    as a distinct labelled entry point so callers naming
    their flows by section don't have to context-switch
    between "this primitive works on state OR storage".

    Use cases:
      * Storage-witness audit fixtures: "what's the keccak
        of the 3rd storage node?"
      * Manual storage-trie walk: caller traversing branch
        children by index materialises each node's hash.
      * Producer-claim verification on the storage side:
        verify a producer-provided list of N expected
        storage node hashes against the witness.

    Calling convention (4 args):
      a0 (input)  : witness.storage ptr
      a1 (input)  : witness.storage len
      a2 (input)  : index (u64)
      a3 (input)  : 32-byte out buffer ptr
      ra (input)  : return

      a0 (output) : 0 = ok / 1 = index OOB
-/
def witnessStorageKeccakAtIndexFunction : String :=
  "witness_storage_keccak_at_index:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp)\n" ++
  "  mv s0, a0                  # section ptr\n" ++
  "  mv s1, a1                  # section_len\n" ++
  "  mv s2, a2                  # index\n" ++
  "  mv s3, a3                  # out buf (32 B)\n" ++
  "  sd zero,  0(s3); sd zero,  8(s3)\n" ++
  "  sd zero, 16(s3); sd zero, 24(s3)\n" ++
  "  beqz s1, .Lwzki_oob\n" ++
  "  lwu t0, 0(s0)              # first inner offset = 4 * N\n" ++
  "  srli s4, t0, 2             # s4 = N\n" ++
  "  bgeu s2, s4, .Lwzki_oob\n" ++
  "  slli t0, s2, 2             # 4 * i\n" ++
  "  add t1, s0, t0\n" ++
  "  lwu t2, 0(t1)              # inner_off_i\n" ++
  "  add a0, s0, t2             # el_i_start\n" ++
  "  addi t3, s2, 1\n" ++
  "  beq t3, s4, .Lwzki_use_end\n" ++
  "  slli t3, t3, 2\n" ++
  "  add t3, s0, t3\n" ++
  "  lwu t4, 0(t3)\n" ++
  "  add t4, s0, t4             # el_i_end\n" ++
  "  j .Lwzki_have_end\n" ++
  ".Lwzki_use_end:\n" ++
  "  add t4, s0, s1             # el_i_end = section_end\n" ++
  ".Lwzki_have_end:\n" ++
  "  sub a1, t4, a0             # el_i_len\n" ++
  "  mv a2, s3                  # out buf\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  li a0, 0\n" ++
  "  j .Lwzki_ret\n" ++
  ".Lwzki_oob:\n" ++
  "  li a0, 1\n" ++
  ".Lwzki_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- `zisk_witness_storage_keccak_at_index`: probe BuildUnit.
    Input layout (at INPUT_ADDR):
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : witness_storage_len (u64 LE)
      bytes 16..24 : index (u64 LE)
      bytes 24..   : witness.storage section bytes
    Output layout (40 bytes):
      bytes  0.. 8 : status (0=ok, 1=OOB)
      bytes  8..40 : keccak256 hash (zero on OOB) -/
def ziskWitnessStorageKeccakAtIndexPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a6, 0x40000000\n" ++
  "  ld a1, 8(a6)                # witness_storage_len\n" ++
  "  ld a2, 16(a6)               # index\n" ++
  "  addi a0, a6, 24             # witness.storage ptr\n" ++
  "  li a3, 0xa0010008           # out buf (32 B)\n" ++
  "  jal ra, witness_storage_keccak_at_index\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lwzki_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  witnessStorageKeccakAtIndexFunction ++ "\n" ++
  ".Lwzki_pdone:"

def ziskWitnessStorageKeccakAtIndexDataSection : String :=
  ".section .data\n" ++
  ".balign 32\n" ++
  "zk3_state:\n" ++
  "  .zero 200"

def ziskWitnessStorageKeccakAtIndexProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskWitnessStorageKeccakAtIndexPrologue
  dataAsm     := ziskWitnessStorageKeccakAtIndexDataSection
}

end EvmAsm.Codegen
