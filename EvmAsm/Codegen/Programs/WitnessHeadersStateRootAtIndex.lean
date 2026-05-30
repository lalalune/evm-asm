/-
  EvmAsm.Codegen.Programs.WitnessHeadersStateRootAtIndex

  Index-based state_root extractor over witness.headers.
  Given (witness.headers, index), find the i-th header RLP
  and extract its state_root field (RLP item 3) into a
  32-byte output buffer.

  Useful for multi-block trust chains: caller has the
  witness.headers section (which holds parent header RLPs
  for BLOCKHASH support) and wants to extract the state_root
  of a specific past block to use for state-trie
  verification.

  No proofs yet -- codegen `String` defs only.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.HashBridge
import EvmAsm.Codegen.Programs.HeaderFields

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## witness_headers_state_root_at_index

    Locate the i-th header RLP in a witness.headers SSZ
    list section and write its state_root field (RLP item 3,
    32 bytes) to the caller's output buffer.

    Composes SSZ inner-offset traversal + K201
    `header_extract_state_root`.

    Use cases:
      * Multi-block trust chain extension: caller has
        verified the chain link `keccak(witness.headers[i])
        == witness.headers[i+1].parent_hash` via #7222, and
        now wants the state_root of header i for state-trie
        verification against witness.state[i].
      * Light-client historical state queries: pull
        state_root_n from witness.headers[k] to verify an
        account / slot proof against block n's state.
      * Per-block state-root audit: chain N calls to extract
        all state_roots across a witness.headers run.

    Calling convention (4 args):
      a0 (input)  : witness.headers ptr
      a1 (input)  : witness.headers len
      a2 (input)  : index (u64)
      a3 (input)  : 32-byte state_root out buffer ptr
      ra (input)  : return

      a0 (output) :
        0 = success (state_root written)
        1 = index out of bounds (buffer zeroed)
        2 = header at index could not be RLP-decoded
        3 = state_root field has unexpected size
-/
def witnessHeadersStateRootAtIndexFunction : String :=
  "witness_headers_state_root_at_index:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a0                  # section ptr\n" ++
  "  mv s1, a1                  # section_len\n" ++
  "  mv s2, a2                  # index\n" ++
  "  mv s3, a3                  # out buf (32 B)\n" ++
  "  sd zero,  0(s3); sd zero,  8(s3); sd zero, 16(s3); sd zero, 24(s3)\n" ++
  "  beqz s1, .Lwhsr_oob\n" ++
  "  lwu t0, 0(s0)\n" ++
  "  srli s4, t0, 2             # s4 = N\n" ++
  "  bgeu s2, s4, .Lwhsr_oob\n" ++
  "  # Compute element i bounds.\n" ++
  "  slli t0, s2, 2\n" ++
  "  add t1, s0, t0\n" ++
  "  lwu t2, 0(t1)              # inner_off_i\n" ++
  "  add s5, s0, t2             # el_i_start\n" ++
  "  addi t3, s2, 1\n" ++
  "  beq t3, s4, .Lwhsr_use_end\n" ++
  "  slli t3, t3, 2\n" ++
  "  add t3, s0, t3\n" ++
  "  lwu t4, 0(t3)\n" ++
  "  add t4, s0, t4\n" ++
  "  j .Lwhsr_have_end\n" ++
  ".Lwhsr_use_end:\n" ++
  "  add t4, s0, s1\n" ++
  ".Lwhsr_have_end:\n" ++
  "  sub s6, t4, s5             # el_i_len\n" ++
  "  mv a0, s5\n" ++
  "  mv a1, s6\n" ++
  "  mv a2, s3                  # output buffer\n" ++
  "  jal ra, header_extract_state_root\n" ++
  "  # header_extract_state_root: 0=ok, 1=parse fail, 2=size fail.\n" ++
  "  beqz a0, .Lwhsr_ret\n" ++
  "  # Remap K201 1->2 and 2->3 to leave 1 for OOB.\n" ++
  "  addi a0, a0, 1\n" ++
  "  j .Lwhsr_ret\n" ++
  ".Lwhsr_oob:\n" ++
  "  li a0, 1\n" ++
  ".Lwhsr_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-- `zisk_witness_headers_state_root_at_index`: probe BuildUnit.
    Input layout (at INPUT_ADDR):
      bytes  0.. 8 : (ziskemu metadata)
      bytes  8..16 : witness_headers_len (u64 LE)
      bytes 16..24 : index (u64 LE)
      bytes 24..   : witness.headers section bytes
    Output layout (40 bytes):
      bytes  0.. 8 : status
      bytes  8..40 : state_root (32 B; zero on early-out) -/
def ziskWitnessHeadersStateRootAtIndexPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a6, 0x40000000\n" ++
  "  ld a1, 8(a6)                # witness_headers_len\n" ++
  "  ld a2, 16(a6)               # index\n" ++
  "  addi a0, a6, 24             # witness.headers ptr\n" ++
  "  li a3, 0xa0010008           # state_root out (32 B)\n" ++
  "  jal ra, witness_headers_state_root_at_index\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lwhsr_pdone\n" ++
  rlpListNthItemFunction ++ "\n" ++
  headerExtractStateRootFunction ++ "\n" ++
  witnessHeadersStateRootAtIndexFunction ++ "\n" ++
  ".Lwhsr_pdone:"

def ziskWitnessHeadersStateRootAtIndexDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "hesr_offset:\n" ++
  "  .zero 8\n" ++
  "hesr_length:\n" ++
  "  .zero 8"

def ziskWitnessHeadersStateRootAtIndexProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskWitnessHeadersStateRootAtIndexPrologue
  dataAsm     := ziskWitnessHeadersStateRootAtIndexDataSection
}

end EvmAsm.Codegen
