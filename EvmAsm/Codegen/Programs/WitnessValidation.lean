/-
  EvmAsm.Codegen.Programs.WitnessValidation

  Witness-section validation primitives that walk an entire SSZ
  list section (witness.state / witness.codes / witness.storage)
  and check structural properties of each element. Distinct
  from `StateCompose.lean` and `EvmOpcodes.lean` (per-address
  composites) -- these primitives operate over the whole
  witness section.

  Currently hosts `witness_codes_validate_lengths`; future
  PRs may add `witness_storage_validate_node_kinds`, etc.

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

/-! ## witness_codes_validate_lengths

    Walk an SSZ `witness.codes` list section and verify every
    entry's byte length is within a caller-supplied cap. Catches
    oversized code blobs up-front, before any account-driven
    lookup attempts to consume them.

    Spec-side rationale: per EIP-170, deployed contract code is
    capped at 24576 bytes (0x6000); per EIP-3860, initcode is
    capped at 49152 bytes (0xc000). Every entry in
    `witness.codes` is supposed to be deployed code referenced
    by some account's `code_hash`, so EIP-170 applies. A
    stateless guest that doesn't catch oversized entries
    up-front could waste keccak cycles hashing absurdly large
    blobs, or surface inconsistent results.

    The cap is passed as an argument so the same primitive can
    cover EIP-170 (24576) for current state and EIP-3860
    (49152) for initcode, or any future tighter bound.

    Distinct from previous witness-iteration primitives:
      * PR `witness_state_validate_node_kinds` -- iterates
        witness.state and checks each entry parses as a valid
        MPT node (not bounded by length).
      * `witness_lookup_by_hash` (K19) -- searches for one hash
        match; doesn't bound per-element length.

    Calling convention:
      a0 (input)  : witness.codes section ptr
      a1 (input)  : section_len (0 ⇒ vacuous-valid)
      a2 (input)  : u64 max_byte_length (per-entry cap;
                    typical: 24576 = EIP-170 limit)
      a3 (input)  : u64 out ptr (n_processed; on success the
                    total count N, on failure the index of the
                    first oversized entry)
      a4 (input)  : u64 out ptr (first_bad_index;
                    0xFFFFFFFFFFFFFFFF on success)
      ra (input)  : return
      a0 (output) :
        0 = all entries within cap (or empty section)
        1 = some entry exceeds `max_byte_length`
-/
def witnessCodesValidateLengthsFunction : String :=
  "witness_codes_validate_lengths:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a0                  # section ptr\n" ++
  "  mv s1, a1                  # section_len\n" ++
  "  mv s2, a2                  # max_byte_length\n" ++
  "  mv s3, a3                  # n_processed out\n" ++
  "  mv s4, a4                  # first_bad_index out\n" ++
  "  sd zero, 0(s3)\n" ++
  "  li t0, -1\n" ++
  "  sd t0, 0(s4)\n" ++
  "  beqz s1, .Lwcvl_ok           # empty section ⇒ vacuous-valid\n" ++
  "  lwu t0, 0(s0)\n" ++
  "  srli s5, t0, 2               # s5 = N\n" ++
  "  li s6, 0                     # s6 = i\n" ++
  ".Lwcvl_loop:\n" ++
  "  beq s6, s5, .Lwcvl_ok\n" ++
  "  # Element i bounds.\n" ++
  "  slli t0, s6, 2\n" ++
  "  add t1, s0, t0\n" ++
  "  lwu t2, 0(t1)                # inner_off_i\n" ++
  "  addi t3, s6, 1\n" ++
  "  beq t3, s5, .Lwcvl_use_end\n" ++
  "  slli t3, t3, 2\n" ++
  "  add t3, s0, t3\n" ++
  "  lwu t4, 0(t3)                # inner_off_{i+1}\n" ++
  "  sub t5, t4, t2               # el_i_len\n" ++
  "  j .Lwcvl_check\n" ++
  ".Lwcvl_use_end:\n" ++
  "  sub t5, s1, t2               # el_i_len = section_len - inner_off_i\n" ++
  ".Lwcvl_check:\n" ++
  "  bgtu t5, s2, .Lwcvl_too_long\n" ++
  "  addi s6, s6, 1\n" ++
  "  j .Lwcvl_loop\n" ++
  ".Lwcvl_too_long:\n" ++
  "  sd s6, 0(s3)                 # n_processed = i\n" ++
  "  sd s6, 0(s4)                 # first_bad_index = i\n" ++
  "  li a0, 1\n" ++
  "  j .Lwcvl_ret\n" ++
  ".Lwcvl_ok:\n" ++
  "  sd s5, 0(s3)                 # n_processed = N\n" ++
  "  li t0, -1\n" ++
  "  sd t0, 0(s4)\n" ++
  "  li a0, 0\n" ++
  ".Lwcvl_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-- `zisk_witness_codes_validate_lengths`: probe BuildUnit.
    Input layout (at INPUT_ADDR):
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : section_len (u64 LE)
      bytes 16..24 : max_byte_length (u64 LE)
      bytes 24..   : witness.codes section bytes
    Output layout:
      bytes  0.. 8 : status (0 ok / 1 some entry too long)
      bytes  8..16 : n_processed (= N on success; first bad index on fail)
      bytes 16..24 : first_bad_index (0xFF..FF on success) -/
def ziskWitnessCodesValidateLengthsPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a5, 0x40000000\n" ++
  "  ld a1, 8(a5)                # section_len\n" ++
  "  ld a2, 16(a5)               # max_byte_length\n" ++
  "  addi a0, a5, 24             # section ptr\n" ++
  "  li a3, 0xa0010008\n" ++
  "  li a4, 0xa0010010\n" ++
  "  jal ra, witness_codes_validate_lengths\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lwcvl_pdone\n" ++
  witnessCodesValidateLengthsFunction ++ "\n" ++
  ".Lwcvl_pdone:"

def ziskWitnessCodesValidateLengthsDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "wcvl_dummy:\n" ++
  "  .zero 8"

def ziskWitnessCodesValidateLengthsProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskWitnessCodesValidateLengthsPrologue
  dataAsm     := ziskWitnessCodesValidateLengthsDataSection
}

end EvmAsm.Codegen
