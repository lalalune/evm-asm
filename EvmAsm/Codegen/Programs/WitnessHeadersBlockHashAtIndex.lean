/-
  EvmAsm.Codegen.Programs.WitnessHeadersBlockHashAtIndex

  Index-based block-hash extractor over witness.headers.
  Given the section and an index i, computes
  keccak256(witness.headers[i]) and returns it.

  The function body is structurally identical to #7215 /
  #7260 (state/storage versions). What's distinct is the
  SEMANTIC: each entry in witness.headers is a full RLP-
  encoded block header, and its keccak IS the canonical
  block hash. This primitive exists as a named entry point
  for callers asking "what's the block hash of the i-th
  historical header in the witness chain?"

  No proofs yet -- codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.HashBridge

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## witness_headers_block_hash_at_index

    Locate the i-th header RLP in a witness.headers SSZ
    list section and return its keccak256 (= canonical
    block hash).

    Use cases:
      * Verify caller-supplied block hash against the i-th
        witness header: extract here, then compare.
      * Manual chain walk: caller maintains the
        (current_block_hash, walk_index) pair and uses
        this primitive to materialise each historical
        block hash by index.
      * Light-client header-chain audit: extract block
        hashes for a UI display, dispute resolution, or
        signature checks against an off-chain log.

    Distinct from #7215 (state) / #7260 (storage) in
    SEMANTIC -- those audit MPT node hashes, this one
    yields the EVM-spec block hash.

    Distinct from #7222: that takes two separate header
    RLPs and checks the chain link; this primitive just
    returns the hash of a single header.

    Calling convention (4 args):
      a0 (input)  : witness.headers ptr
      a1 (input)  : witness.headers len
      a2 (input)  : index (u64)
      a3 (input)  : 32-byte block_hash out buffer ptr
      ra (input)  : return

      a0 (output) : 0 = ok / 1 = index OOB (buffer zeroed)
-/
def witnessHeadersBlockHashAtIndexFunction : String :=
  "witness_headers_block_hash_at_index:\n" ++
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
  "  beqz s1, .Lwhbh_oob\n" ++
  "  lwu t0, 0(s0)\n" ++
  "  srli s4, t0, 2             # s4 = N\n" ++
  "  bgeu s2, s4, .Lwhbh_oob\n" ++
  "  slli t0, s2, 2\n" ++
  "  add t1, s0, t0\n" ++
  "  lwu t2, 0(t1)\n" ++
  "  add a0, s0, t2             # header_i start\n" ++
  "  addi t3, s2, 1\n" ++
  "  beq t3, s4, .Lwhbh_use_end\n" ++
  "  slli t3, t3, 2\n" ++
  "  add t3, s0, t3\n" ++
  "  lwu t4, 0(t3)\n" ++
  "  add t4, s0, t4             # header_i end\n" ++
  "  j .Lwhbh_have_end\n" ++
  ".Lwhbh_use_end:\n" ++
  "  add t4, s0, s1\n" ++
  ".Lwhbh_have_end:\n" ++
  "  sub a1, t4, a0             # header_i len\n" ++
  "  mv a2, s3                  # out buf\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  li a0, 0\n" ++
  "  j .Lwhbh_ret\n" ++
  ".Lwhbh_oob:\n" ++
  "  li a0, 1\n" ++
  ".Lwhbh_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- `zisk_witness_headers_block_hash_at_index`: probe BuildUnit.
    Input layout (at INPUT_ADDR):
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : witness_headers_len (u64 LE)
      bytes 16..24 : index (u64 LE)
      bytes 24..   : witness.headers section bytes
    Output layout (40 bytes):
      bytes  0.. 8 : status (0 = ok, 1 = OOB)
      bytes  8..40 : block_hash (32 B; zero on OOB) -/
def ziskWitnessHeadersBlockHashAtIndexPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a6, 0x40000000\n" ++
  "  ld a1, 8(a6)                # witness_headers_len\n" ++
  "  ld a2, 16(a6)               # index\n" ++
  "  addi a0, a6, 24             # witness.headers ptr\n" ++
  "  li a3, 0xa0010008           # out buf (32 B)\n" ++
  "  jal ra, witness_headers_block_hash_at_index\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lwhbh_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  witnessHeadersBlockHashAtIndexFunction ++ "\n" ++
  ".Lwhbh_pdone:"

def ziskWitnessHeadersBlockHashAtIndexDataSection : String :=
  ".section .data\n" ++
  ".balign 32\n" ++
  "zk3_state:\n" ++
  "  .zero 200"

def ziskWitnessHeadersBlockHashAtIndexProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskWitnessHeadersBlockHashAtIndexPrologue
  dataAsm     := ziskWitnessHeadersBlockHashAtIndexDataSection
}

end EvmAsm.Codegen
