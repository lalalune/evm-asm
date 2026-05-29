/-
  EvmAsm.Codegen.Programs.WitnessValidation

  Witness-section validation primitives that walk an entire SSZ
  list section (witness.state / witness.codes / witness.storage)
  and check structural properties of each element. Distinct
  from `StateCompose.lean` and `EvmOpcodes.lean` (per-address
  composites) -- these primitives operate over the whole
  witness section.

  Currently hosts `witness_state_validate_node_kinds`; future
  PRs may add `witness_codes_validate_lengths`,
  `witness_storage_validate_node_kinds`, etc.

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

/-! ## witness_state_validate_node_kinds

    Walk an SSZ `witness.state` list section and call K21
    `mpt_node_kind` on every entry. Verifies that every entry
    parses as a valid MPT node (Leaf / Extension / Branch).
    Reports the index of the first malformed entry, or the
    total node count if all parse successfully.

    Spec-side rationale: every entry in `witness.state` is
    supposed to be the canonical RLP encoding of an MPT node
    on the proof path from header.state_root to some account.
    A witness with a non-parseable entry can't be safely
    consumed by `mpt_walk` -- this primitive catches structural
    failures up-front rather than discovering them mid-trie-walk.

    Distinct from previous witness-iteration primitives:
      * `witness_lookup_by_hash` (K19) -- searches by keccak
        match; stops on first hit, doesn't validate structure.
      * `validate_witness_state_contains_root` (PR #7143) --
        checks one specific hash is reachable; doesn't validate
        all entries.
      * `witness_headers_chain_validate` (PR #7158) -- iterates
        but checks parent-hash linkage between consecutive
        headers, not per-element MPT-node structure.

    Calling convention:
      a0 (input)  : witness.state section ptr
      a1 (input)  : section_len (0 ⇒ vacuous-valid)
      a2 (input)  : u64 out ptr (n_processed; on success the
                    total node count N, on failure the index of
                    the first invalid node)
      a3 (input)  : u64 out ptr (first_bad_index;
                    0xFFFFFFFFFFFFFFFF on success, else the
                    failing element's index)
      ra (input)  : return
      a0 (output) :
        0 = all entries parse as valid MPT nodes
        1 = some entry failed to parse (`mpt_node_kind` = 3)
-/
def witnessStateValidateNodeKindsFunction : String :=
  "witness_state_validate_node_kinds:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a0                  # section ptr\n" ++
  "  mv s1, a1                  # section_len\n" ++
  "  mv s2, a2                  # n_processed out\n" ++
  "  mv s3, a3                  # first_bad_index out\n" ++
  "  sd zero, 0(s2)\n" ++
  "  li t0, -1\n" ++
  "  sd t0, 0(s3)\n" ++
  "  beqz s1, .Lwsvn_ok           # empty section ⇒ vacuous-valid\n" ++
  "  lwu t0, 0(s0)\n" ++
  "  srli s4, t0, 2               # s4 = N\n" ++
  "  li s5, 0                     # s5 = i\n" ++
  ".Lwsvn_loop:\n" ++
  "  beq s5, s4, .Lwsvn_ok\n" ++
  "  # Element i bounds.\n" ++
  "  slli t0, s5, 2\n" ++
  "  add t1, s0, t0\n" ++
  "  lwu t2, 0(t1)                # inner_off_i\n" ++
  "  add a0, s0, t2               # el_i_start\n" ++
  "  addi t3, s5, 1\n" ++
  "  beq t3, s4, .Lwsvn_use_end\n" ++
  "  slli t3, t3, 2\n" ++
  "  add t3, s0, t3\n" ++
  "  lwu t4, 0(t3)\n" ++
  "  add t4, s0, t4               # el_i_end\n" ++
  "  j .Lwsvn_have_end\n" ++
  ".Lwsvn_use_end:\n" ++
  "  add t4, s0, s1\n" ++
  ".Lwsvn_have_end:\n" ++
  "  sub a1, t4, a0               # el_i_len\n" ++
  "  jal ra, mpt_node_kind\n" ++
  "  li t0, 3\n" ++
  "  beq a0, t0, .Lwsvn_parse_fail\n" ++
  "  addi s5, s5, 1\n" ++
  "  j .Lwsvn_loop\n" ++
  ".Lwsvn_parse_fail:\n" ++
  "  sd s5, 0(s2)                 # n_processed = i\n" ++
  "  sd s5, 0(s3)                 # first_bad_index = i\n" ++
  "  li a0, 1\n" ++
  "  j .Lwsvn_ret\n" ++
  ".Lwsvn_ok:\n" ++
  "  sd s4, 0(s2)                 # n_processed = N (full)\n" ++
  "  li t0, -1\n" ++
  "  sd t0, 0(s3)                 # first_bad_index = -1\n" ++
  "  li a0, 0\n" ++
  ".Lwsvn_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-- `zisk_witness_state_validate_node_kinds`: probe BuildUnit.
    Input layout (at INPUT_ADDR):
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : section_len (u64 LE)
      bytes 16..   : witness.state section bytes
    Output layout:
      bytes  0.. 8 : status (0 ok / 1 parse fail)
      bytes  8..16 : n_processed (= N on success; first bad index on fail)
      bytes 16..24 : first_bad_index (0xFF..FF on success) -/
def ziskWitnessStateValidateNodeKindsPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a5, 0x40000000\n" ++
  "  ld a1, 8(a5)                # section_len\n" ++
  "  addi a0, a5, 16             # section ptr\n" ++
  "  li a2, 0xa0010008\n" ++
  "  li a3, 0xa0010010\n" ++
  "  jal ra, witness_state_validate_node_kinds\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lwsvn_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  mptNodeKindFunction ++ "\n" ++
  witnessStateValidateNodeKindsFunction ++ "\n" ++
  ".Lwsvn_pdone:"

def ziskWitnessStateValidateNodeKindsDataSection : String :=
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

def ziskWitnessStateValidateNodeKindsProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskWitnessStateValidateNodeKindsPrologue
  dataAsm     := ziskWitnessStateValidateNodeKindsDataSection
}

end EvmAsm.Codegen
