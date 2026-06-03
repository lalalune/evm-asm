/-
  EvmAsm.Codegen.Programs.RuntimeAccountWitness

  Probes for the runtime dispatcher's account-witness input context.
-/

import EvmAsm.Codegen.Dispatch
import EvmAsm.Codegen.Programs.EvmOpcodes

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/--
Runtime-layout probe for the shared account-witness context.

Input is the normal `scripts/pack-bytecode.py` runtime bytecode payload. The
bytecode segment is interpreted as the 20-byte address to query. The probe runs
the same setup code as `runtime_dispatcher`, then calls
`extcodehash_at_header_state_root` with that address and the parent-header /
witness.state pointers that setup stored in `evm_env`. This validates the
reusable context without changing any opcode handler wiring.

Output:
  bytes  0.. 8 : helper status
  bytes  8..40 : EXTCODEHASH result
-/
def runtimeAccountWitnessExtcodehashPrologue : String :=
  emitRuntimeDispatcherSetup ++ "
" ++
  "  ld a0, 576(x20)
" ++       -- header ptr
  "  ld a1, 584(x20)
" ++       -- header len
  "  beqz a1, .Lraw_ech_no_context
" ++
  "  mv a2, x21
" ++       -- address ptr: bytecode segment payload
  "  ld a3, 592(x20)
" ++       -- witness.state ptr
  "  ld a4, 600(x20)
" ++       -- witness.state len
  "  li a5, 0xa0010008
" ++     -- output hash
  "  jal ra, extcodehash_at_header_state_root
" ++
  "  li t0, 0xa0010000
" ++
  "  sd a0, 0(t0)
" ++
  "  j .Lraw_ech_done
" ++
  ".Lraw_ech_no_context:
" ++
  "  li t0, 0xa0010000
" ++
  "  sd zero, 0(t0)
" ++
  "  sd zero, 8(t0)
" ++
  "  sd zero, 16(t0)
" ++
  "  sd zero, 24(t0)
" ++
  "  sd zero, 32(t0)
" ++
  "  j .Lraw_ech_done
" ++
  zkvmKeccak256Function ++ "
" ++
  witnessLookupByHashFunction ++ "
" ++
  rlpListNthItemFunction ++ "
" ++
  mptNodeKindFunction ++ "
" ++
  mptBranchChildFunction ++ "
" ++
  hpDecodeNibblesFunction ++ "
" ++
  bytesToNibblesFunction ++ "
" ++
  mptWalkFunction ++ "
" ++
  mptLookupByKeyFunction ++ "
" ++
  accountDecodeFunction ++ "
" ++
  accountAtAddressFunction ++ "
" ++
  headerExtractStateRootFunction ++ "
" ++
  extcodehashAtHeaderStateRootFunction ++ "
" ++
  ".Lraw_ech_done:"


/-- Minimal `.data` section for runtime account-witness probes.

This mirrors the runtime dispatcher's context-carrying data without emitting a
jump table, so the probe can link without opcode handler labels. -/
def runtimeAccountWitnessProbeDataSection : String :=
  ".section .data\n" ++
  ".balign 32\n" ++
  "evm_stack_low:\n" ++
  "  .zero 256\n" ++
  "evm_stack_top:\n" ++
  ".balign 32\n" ++
  "evm_memory:\n" ++
  "  .zero 0x8000\n" ++
  ".balign 8\n" ++
  "evm_env:\n" ++
  "  .zero 624\n" ++
  ".balign 8\n" ++
  "evm_blob_hashes:\n" ++
  "  .zero 512\n" ++
  ".balign 8\n" ++
  "evm_block_hashes:\n" ++
  "  .zero 8192\n" ++
  ".balign 8\n" ++
  "evm_event_logs:\n" ++
  "  .zero 4096\n" ++
  emitPrecompileFrameData ++
  emitSha256Data ++
  ".balign 8\n" ++
  "zk3_state:\n" ++
  "  .zero 200\n" ++
  emitRuntimeAccountWitnessData ++
  ".balign 16\n" ++
  "lp64_stack:\n" ++
  "  .zero 262144\n" ++
  "lp64_sp_top:\n"

def runtimeAccountWitnessExtcodehashProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := runtimeAccountWitnessExtcodehashPrologue
  dataAsm     := runtimeAccountWitnessProbeDataSection
}

end EvmAsm.Codegen
