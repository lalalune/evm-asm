/-
  EvmAsm.Codegen.Programs.WitnessHeadersFindIndexByBlockHash

  Pure search primitive: given a block_hash and
  witness.headers, return the index i such that
  keccak256(witness.headers[i]) == block_hash, or signal
  not-found.

  Hash -> index inverse of #7304 (which is index -> hash).
  Useful building block for hash-keyed flows that need to
  know the position (e.g. for downstream chain-link checks
  against neighbouring indices).

  No proofs yet -- codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.HashBridge

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## witness_headers_find_index_by_block_hash

    Iterate the witness.headers SSZ list section, keccak
    each entry, and return the first index i where
    keccak(headers[i]) == block_hash.

    On miss, sets index to 0 and returns status 1; caller
    distinguishes via status, not via the written index
    (so the output buffer's contents on miss aren't
    semantically meaningful).

    Inverse of #7304: that returns hash for a given index;
    this returns index for a given hash.

    Use cases:
      * Translate a hash-keyed query into an index-keyed
        downstream call (e.g. caller has block_hash, wants
        to chain into #7283 / #7296 which take indices).
      * Detect whether a claimed block_hash is in the
        witness chain without doing the full account walk
        of #7307.
      * Audit: find which position in the chain the trusted
        anchor block sits at.

    Calling convention (4 args):
      a0 (input)  : block_hash ptr (32 bytes)
      a1 (input)  : witness.headers ptr
      a2 (input)  : witness.headers len
      a3 (input)  : u64 index out ptr
      ra (input)  : return

      a0 (output) :
        0 = found (index written)
        1 = block_hash not in witness.headers
-/
def witnessHeadersFindIndexByBlockHashFunction : String :=
  "witness_headers_find_index_by_block_hash:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a0                  # block_hash ptr\n" ++
  "  mv s1, a1                  # section ptr\n" ++
  "  mv s2, a2                  # section_len\n" ++
  "  mv s3, a3                  # index out\n" ++
  "  sd zero, 0(s3)\n" ++
  "  beqz s2, .Lwhfi_miss\n" ++
  "  lwu t0, 0(s1)\n" ++
  "  srli s4, t0, 2             # s4 = N\n" ++
  "  li s5, 0                   # s5 = i\n" ++
  ".Lwhfi_loop:\n" ++
  "  beq s5, s4, .Lwhfi_miss\n" ++
  "  slli t0, s5, 2\n" ++
  "  add t1, s1, t0\n" ++
  "  lwu t2, 0(t1)\n" ++
  "  add a0, s1, t2             # el_i_start\n" ++
  "  addi t3, s5, 1\n" ++
  "  beq t3, s4, .Lwhfi_use_end\n" ++
  "  slli t3, t3, 2\n" ++
  "  add t3, s1, t3\n" ++
  "  lwu t4, 0(t3)\n" ++
  "  add t4, s1, t4             # el_i_end\n" ++
  "  j .Lwhfi_have_end\n" ++
  ".Lwhfi_use_end:\n" ++
  "  add t4, s1, s2\n" ++
  ".Lwhfi_have_end:\n" ++
  "  sub a1, t4, a0             # el_i_len\n" ++
  "  la a2, whfi_scratch_hash\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  la t0, whfi_scratch_hash\n" ++
  "  mv t1, s0\n" ++
  "  ld t2,  0(t0); ld t3,  0(t1); bne t2, t3, .Lwhfi_step\n" ++
  "  ld t2,  8(t0); ld t3,  8(t1); bne t2, t3, .Lwhfi_step\n" ++
  "  ld t2, 16(t0); ld t3, 16(t1); bne t2, t3, .Lwhfi_step\n" ++
  "  ld t2, 24(t0); ld t3, 24(t1); bne t2, t3, .Lwhfi_step\n" ++
  "  # Match.\n" ++
  "  sd s5, 0(s3)\n" ++
  "  li a0, 0\n" ++
  "  j .Lwhfi_ret\n" ++
  ".Lwhfi_step:\n" ++
  "  addi s5, s5, 1\n" ++
  "  j .Lwhfi_loop\n" ++
  ".Lwhfi_miss:\n" ++
  "  li a0, 1\n" ++
  ".Lwhfi_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-- `zisk_witness_headers_find_index_by_block_hash`: probe BuildUnit.
    Input layout (at INPUT_ADDR):
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : witness_headers_len (u64 LE)
      bytes 16..48 : block_hash (32 bytes)
      bytes 48..   : witness.headers section bytes
    Output layout (16 bytes):
      bytes  0.. 8 : status (0 = found, 1 = miss)
      bytes  8..16 : index (u64; 0 on miss) -/
def ziskWitnessHeadersFindIndexByBlockHashPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a6, 0x40000000\n" ++
  "  ld a2, 8(a6)                # witness_headers_len\n" ++
  "  addi a0, a6, 16             # block_hash ptr\n" ++
  "  addi a1, a6, 48             # witness.headers ptr\n" ++
  "  li a3, 0xa0010008           # index out\n" ++
  "  jal ra, witness_headers_find_index_by_block_hash\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lwhfi_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  witnessHeadersFindIndexByBlockHashFunction ++ "\n" ++
  ".Lwhfi_pdone:"

def ziskWitnessHeadersFindIndexByBlockHashDataSection : String :=
  ".section .data\n" ++
  ".balign 32\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  ".balign 32\n" ++
  "whfi_scratch_hash:\n" ++
  "  .zero 32"

def ziskWitnessHeadersFindIndexByBlockHashProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskWitnessHeadersFindIndexByBlockHashPrologue
  dataAsm     := ziskWitnessHeadersFindIndexByBlockHashDataSection
}

end EvmAsm.Codegen
