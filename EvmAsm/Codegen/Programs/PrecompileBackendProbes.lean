/-
  EvmAsm.Codegen.Programs.PrecompileBackendProbes

  Standalone backend probes for zkvm accelerator wrappers used by EVM
  precompile runtime bodies.
-/

import EvmAsm.Codegen.Layout
import EvmAsm.Rv64.Program

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-- Linkable bare-RV64 wrapper for `zkvm_bls12_g1_add(p1, p2, result)`.
    The zkvm-standards C ABI fixes argument registers as a0/a1/a2 and
    return status in a0; this shim supplies the concrete accelerator selector
    in t0/x5 and delegates to the host via ECALL. -/
def zkvmBls12G1AddEcallWrapper : String :=
  ".globl zkvm_bls12_g1_add\n" ++
  "zkvm_bls12_g1_add:\n" ++
  "  li t0, 0x10b\n" ++
  "  ecall\n" ++
  "  ret"

/-- Probe driver for the BLS12 G1 ADD wrapper. It initializes two 96-byte
    zero point buffers and a 96-byte result buffer, calls the wrapper, then
    writes a compact record at OUTPUT_ADDR:

      OUTPUT+0   : returned zkvm_status as u64
      OUTPUT+8   : first 8 bytes of result buffer
      OUTPUT+16  : second 8 bytes of result buffer

    The shell harness classifies `0` (EOK) and `-1` (EFAIL) as a linked
    backend return, and treats emulator failure as a not-ready backend route. -/
def ziskBls12G1AddBackendProbePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  la t0, bls12_g1_add_result\n" ++
  "  li t1, 12\n" ++
  "  li t2, -6148914691236517206\n" ++ -- 0xaaaaaaaaaaaaaaaa
  ".Lbls12_g1_add_fill_result:\n" ++
  "  sd t2, 0(t0)\n" ++
  "  addi t0, t0, 8\n" ++
  "  addi t1, t1, -1\n" ++
  "  bnez t1, .Lbls12_g1_add_fill_result\n" ++
  "  la a0, bls12_g1_add_p1\n" ++
  "  la a1, bls12_g1_add_p2\n" ++
  "  la a2, bls12_g1_add_result\n" ++
  "  jal ra, zkvm_bls12_g1_add\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  la t1, bls12_g1_add_result\n" ++
  "  ld t2, 0(t1)\n" ++
  "  sd t2, 8(t0)\n" ++
  "  ld t2, 8(t1)\n" ++
  "  sd t2, 16(t0)\n" ++
  "  j .Lbls12_g1_add_done\n" ++
  zkvmBls12G1AddEcallWrapper ++ "\n" ++
  ".Lbls12_g1_add_done:"

def ziskBls12G1AddBackendProbeDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "bls12_g1_add_p1:\n" ++
  "  .zero 96\n" ++
  "bls12_g1_add_p2:\n" ++
  "  .zero 96\n" ++
  "bls12_g1_add_result:\n" ++
  "  .zero 96"

def ziskBls12G1AddBackendProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBls12G1AddBackendProbePrologue
  dataAsm     := ziskBls12G1AddBackendProbeDataSection
}

end EvmAsm.Codegen
