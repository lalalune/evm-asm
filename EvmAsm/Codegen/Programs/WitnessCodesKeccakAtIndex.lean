/-
  EvmAsm.Codegen.Programs.WitnessCodesKeccakAtIndex

  Fourth index -> keccak primitive, completing the
  symmetric set:
    #7215  witness_state_keccak_at_index
    #7260  witness_storage_keccak_at_index
    #7304  witness_headers_block_hash_at_index
    this   witness_codes_keccak_at_index

  Body identical to siblings; distinct named primitive for
  call-site clarity and separate ELF.

  No proofs yet -- codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.HashBridge

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## witness_codes_keccak_at_index

    Read the i-th entry of a witness.codes SSZ list section
    and return its keccak256 -- the canonical
    EIP-spec code_hash of that bytecode.

    Distinct semantic from siblings:
      * #7215 / #7260: MPT node hashes
      * #7304: canonical block hash
      * THIS: canonical code_hash (== keccak of deployed
        bytecode, the same value stored in an account
        struct's code_hash field)

    Use cases:
      * Witness audit: "what's the code_hash of the i-th
        contract in witness.codes?"
      * Producer-claim verification: caller has an off-chain
        list of expected code_hashes; this primitive
        materialises the actual hashes from witness in
        order.
      * Reverse-direction lookup: caller has just retrieved
        (offset, length) via #7333 and wants to confirm the
        keccak self-consistency by index.

    Calling convention (4 args):
      a0 (input)  : witness.codes ptr
      a1 (input)  : witness.codes len
      a2 (input)  : index (u64)
      a3 (input)  : 32-byte out buffer ptr
      ra (input)  : return

      a0 (output) : 0 = ok / 1 = index OOB
-/
def witnessCodesKeccakAtIndexFunction : String :=
  "witness_codes_keccak_at_index:\n" ++
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
  "  beqz s1, .Lwcki_oob\n" ++
  "  lwu t0, 0(s0)\n" ++
  "  srli s4, t0, 2             # s4 = N\n" ++
  "  bgeu s2, s4, .Lwcki_oob\n" ++
  "  slli t0, s2, 2\n" ++
  "  add t1, s0, t0\n" ++
  "  lwu t2, 0(t1)\n" ++
  "  add a0, s0, t2             # el_i_start\n" ++
  "  addi t3, s2, 1\n" ++
  "  beq t3, s4, .Lwcki_use_end\n" ++
  "  slli t3, t3, 2\n" ++
  "  add t3, s0, t3\n" ++
  "  lwu t4, 0(t3)\n" ++
  "  add t4, s0, t4             # el_i_end\n" ++
  "  j .Lwcki_have_end\n" ++
  ".Lwcki_use_end:\n" ++
  "  add t4, s0, s1\n" ++
  ".Lwcki_have_end:\n" ++
  "  sub a1, t4, a0\n" ++
  "  mv a2, s3\n" ++
  "  jal ra, zkvm_keccak256\n" ++
  "  li a0, 0\n" ++
  "  j .Lwcki_ret\n" ++
  ".Lwcki_oob:\n" ++
  "  li a0, 1\n" ++
  ".Lwcki_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- `zisk_witness_codes_keccak_at_index`: probe BuildUnit.
    Input layout (at INPUT_ADDR):
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : witness_codes_len (u64 LE)
      bytes 16..24 : index (u64 LE)
      bytes 24..   : witness.codes section bytes
    Output layout (40 bytes):
      bytes  0.. 8 : status (0=ok, 1=OOB)
      bytes  8..40 : keccak256 / code_hash (32 B; zero on OOB) -/
def ziskWitnessCodesKeccakAtIndexPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a6, 0x40000000\n" ++
  "  ld a1, 8(a6)                # witness_codes_len\n" ++
  "  ld a2, 16(a6)               # index\n" ++
  "  addi a0, a6, 24             # witness.codes ptr\n" ++
  "  li a3, 0xa0010008           # out buf (32 B)\n" ++
  "  jal ra, witness_codes_keccak_at_index\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lwcki_pdone\n" ++
  zkvmKeccak256Function ++ "\n" ++
  witnessCodesKeccakAtIndexFunction ++ "\n" ++
  ".Lwcki_pdone:"

def ziskWitnessCodesKeccakAtIndexDataSection : String :=
  ".section .data\n" ++
  ".balign 32\n" ++
  "zk3_state:\n" ++
  "  .zero 200"

def ziskWitnessCodesKeccakAtIndexProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskWitnessCodesKeccakAtIndexPrologue
  dataAsm     := ziskWitnessCodesKeccakAtIndexDataSection
}

end EvmAsm.Codegen
