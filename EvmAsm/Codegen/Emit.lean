/-
  EvmAsm.Codegen.Emit

  Pretty-print `Instr` and `Program` as GNU-as RV64IM mnemonics.

  M0 only needs the constructors used by the smoke target
  (`LI`, `ADD`, `ADDI`, `MV`, `NOP`, `ECALL`, `EBREAK`, `FENCE`); the rest fall
  through to a `# TODO(M1)` marker which `riscv64-unknown-elf-as` will reject
  loudly once a real Program tries to use it. Coverage is broadened in M1.

  Emission is a one-way output channel; it carries no proofs and is not part
  of the trusted kernel surface (see CODEGEN.md §"Codegen is not verified").
-/

import EvmAsm.Rv64.Program

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-- Render a register as the canonical `xNN` mnemonic. Matches the existing
    `ToString Reg` instance at `EvmAsm/Rv64/Basic.lean:90-91`. -/
def emitReg (r : Reg) : String := toString r

/-- Render a single RV64IM instruction as one GNU-as line (no leading indent). -/
def emitInstr : Instr → String
  | .LI    rd imm        => s!"li {emitReg rd}, {imm.toInt}"
  | .ADD   rd rs1 rs2    => s!"add {emitReg rd}, {emitReg rs1}, {emitReg rs2}"
  | .ADDI  rd rs1 imm    => s!"addi {emitReg rd}, {emitReg rs1}, {imm.toInt}"
  | .MV    rd rs         => s!"mv {emitReg rd}, {emitReg rs}"
  | .NOP                 => "nop"
  | .ECALL               => "ecall"
  | .EBREAK              => "ebreak"
  | .FENCE               => "fence"
  | i                    => s!"# TODO(M1): emit {repr i}"

/-- Render a `Program` as one mnemonic per line, each indented two spaces. -/
def emitProgram (p : Program) : String :=
  String.intercalate "\n" (p.map (fun i => "  " ++ emitInstr i))

end EvmAsm.Codegen
