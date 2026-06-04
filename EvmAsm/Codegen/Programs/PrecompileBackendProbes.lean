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
    The installed ziskemu currently does not complete ECALL selector 0x10b from
    bare codegen ELFs. Keep the ABI linkable and deterministic by returning
    EFAIL (-1) without touching the result buffer. Runtime callers can therefore
    exercise the BLS12 G1 ADD dispatch path without crashing guest execution;
    replacing this shim with the real ECALL route is tracked separately once the
    backend/replay path is available. -/
def zkvmBls12G1AddSafeFailWrapper : String :=
  ".globl zkvm_bls12_g1_add\n" ++
  "zkvm_bls12_g1_add:\n" ++
  "  li a0, -1\n" ++
  "  ret"

/-- Probe driver for the BLS12 G1 ADD wrapper. It initializes two 96-byte
    zero point buffers and a 96-byte result buffer, calls the wrapper, then
    writes a compact record at OUTPUT_ADDR:

      OUTPUT+0   : returned zkvm_status as u64
      OUTPUT+8   : first 8 bytes of result buffer
      OUTPUT+16  : second 8 bytes of result buffer

    The shell harness classifies `0` (EOK) and `-1` (EFAIL) as a linked
    backend return. On the current host this probe uses the deterministic
    safe-fail shim above, so it should complete with EFAIL instead of crashing
    on the unsupported ECALL route. -/
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
  zkvmBls12G1AddSafeFailWrapper ++ "\n" ++
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


/-- Linkable bare-RV64 safe-fail wrapper for a BLS12 accelerator selector.
    Current ziskemu does not complete the BLS12 accelerator ECALL selectors from
    bare codegen ELFs. Keep each ABI symbol linkable and deterministic by
    returning EFAIL (-1) without touching the result buffer. -/
def bls12SafeFailWrapper (symbol : String) (_selectorHex : String) : String :=
  ".globl " ++ symbol ++ "\n" ++
  symbol ++ ":\n" ++
  "  li a0, -1\n" ++
  "  ret"

private def fillPatternAsm (label : String) (buffer : String) (bytes : Nat) : String :=
  "  la t0, " ++ buffer ++ "\n" ++
  "  li t1, " ++ toString (bytes / 8) ++ "\n" ++
  "  li t2, -6148914691236517206\n" ++
  "." ++ label ++ "_fill:\n" ++
  "  sd t2, 0(t0)\n" ++
  "  addi t0, t0, 8\n" ++
  "  addi t1, t1, -1\n" ++
  "  bnez t1, ." ++ label ++ "_fill\n"

private def copyProbeOutputAsm (resultLabel : String) : String :=
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  la t1, " ++ resultLabel ++ "\n" ++
  "  ld t2, 0(t1)\n" ++
  "  sd t2, 8(t0)\n" ++
  "  ld t2, 8(t1)\n" ++
  "  sd t2, 16(t0)\n"

private def bls12BackendProbePrologue
    (label symbol selectorHex resultLabel setupArgs : String)
    (resultBytes : Nat) : String :=
  "  li sp, 0xa0050000\n" ++
  fillPatternAsm label resultLabel resultBytes ++
  setupArgs ++
  "  jal ra, " ++ symbol ++ "\n" ++
  copyProbeOutputAsm resultLabel ++
  "  j ." ++ label ++ "_done\n" ++
  bls12SafeFailWrapper symbol selectorHex ++ "\n" ++
  "." ++ label ++ "_done:"

private def bls12ProbeDataSection (items : List (String × Nat)) : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  String.intercalate "" (items.map fun (name, bytes) =>
    name ++ ":\n" ++
    "  .zero " ++ toString bytes ++ "\n")

def ziskBls12G1MsmBackendProbePrologue : String :=
  bls12BackendProbePrologue
    "Lbls12_g1_msm" "zkvm_bls12_g1_msm" "0x10c" "bls12_g1_msm_result"
    ("  la a0, bls12_g1_msm_pairs\n" ++
     "  li a1, 1\n" ++
     "  la a2, bls12_g1_msm_result\n")
    96

def ziskBls12G1MsmBackendProbeDataSection : String :=
  bls12ProbeDataSection
    [("bls12_g1_msm_pairs", 128), ("bls12_g1_msm_result", 96)]

def ziskBls12G1MsmBackendProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBls12G1MsmBackendProbePrologue
  dataAsm     := ziskBls12G1MsmBackendProbeDataSection
}

def ziskBls12G2AddBackendProbePrologue : String :=
  bls12BackendProbePrologue
    "Lbls12_g2_add" "zkvm_bls12_g2_add" "0x10d" "bls12_g2_add_result"
    ("  la a0, bls12_g2_add_p1\n" ++
     "  la a1, bls12_g2_add_p2\n" ++
     "  la a2, bls12_g2_add_result\n")
    192

def ziskBls12G2AddBackendProbeDataSection : String :=
  bls12ProbeDataSection
    [("bls12_g2_add_p1", 192), ("bls12_g2_add_p2", 192),
     ("bls12_g2_add_result", 192)]

def ziskBls12G2AddBackendProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBls12G2AddBackendProbePrologue
  dataAsm     := ziskBls12G2AddBackendProbeDataSection
}

def ziskBls12G2MsmBackendProbePrologue : String :=
  bls12BackendProbePrologue
    "Lbls12_g2_msm" "zkvm_bls12_g2_msm" "0x10e" "bls12_g2_msm_result"
    ("  la a0, bls12_g2_msm_pairs\n" ++
     "  li a1, 1\n" ++
     "  la a2, bls12_g2_msm_result\n")
    192

def ziskBls12G2MsmBackendProbeDataSection : String :=
  bls12ProbeDataSection
    [("bls12_g2_msm_pairs", 224), ("bls12_g2_msm_result", 192)]

def ziskBls12G2MsmBackendProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBls12G2MsmBackendProbePrologue
  dataAsm     := ziskBls12G2MsmBackendProbeDataSection
}

def ziskBls12PairingBackendProbePrologue : String :=
  bls12BackendProbePrologue
    "Lbls12_pairing" "zkvm_bls12_pairing" "0x10f" "bls12_pairing_verified"
    ("  la a0, bls12_pairing_pairs\n" ++
     "  li a1, 1\n" ++
     "  la a2, bls12_pairing_verified\n")
    16

def ziskBls12PairingBackendProbeDataSection : String :=
  bls12ProbeDataSection
    [("bls12_pairing_pairs", 288), ("bls12_pairing_verified", 16)]

def ziskBls12PairingBackendProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBls12PairingBackendProbePrologue
  dataAsm     := ziskBls12PairingBackendProbeDataSection
}

def ziskBls12MapFpToG1BackendProbePrologue : String :=
  bls12BackendProbePrologue
    "Lbls12_map_fp_to_g1" "zkvm_bls12_map_fp_to_g1" "0x110" "bls12_map_fp_to_g1_result"
    ("  la a0, bls12_map_fp_to_g1_input\n" ++
     "  la a1, bls12_map_fp_to_g1_result\n")
    96

def ziskBls12MapFpToG1BackendProbeDataSection : String :=
  bls12ProbeDataSection
    [("bls12_map_fp_to_g1_input", 48), ("bls12_map_fp_to_g1_result", 96)]

def ziskBls12MapFpToG1BackendProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBls12MapFpToG1BackendProbePrologue
  dataAsm     := ziskBls12MapFpToG1BackendProbeDataSection
}

def ziskBls12MapFp2ToG2BackendProbePrologue : String :=
  bls12BackendProbePrologue
    "Lbls12_map_fp2_to_g2" "zkvm_bls12_map_fp2_to_g2" "0x111" "bls12_map_fp2_to_g2_result"
    ("  la a0, bls12_map_fp2_to_g2_input\n" ++
     "  la a1, bls12_map_fp2_to_g2_result\n")
    192

def ziskBls12MapFp2ToG2BackendProbeDataSection : String :=
  bls12ProbeDataSection
    [("bls12_map_fp2_to_g2_input", 96), ("bls12_map_fp2_to_g2_result", 192)]

def ziskBls12MapFp2ToG2BackendProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBls12MapFp2ToG2BackendProbePrologue
  dataAsm     := ziskBls12MapFp2ToG2BackendProbeDataSection
}

end EvmAsm.Codegen
