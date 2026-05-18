/-
  EvmAsm.Codegen.Layout

  GNU-as program-layout templates: the `_start` wrapper, halt stubs, and
  memory-region constants.

  Halt convention is parametric (see CODEGEN.md §"Locked decisions"):
    `.sp1`     — matches the verified `step_ecall_halt`
                 (`EvmAsm/Rv64/Execution.lean:611-615`): `ECALL` with `t0 = 0`.
    `.linux93` — matches Zisk's `elf-regressions/simple_add`:
                 `ECALL` with `a7 = 93`, `a0 = 0`.

  The halt stubs are emitted as raw GNU-as text rather than as `Instr` values
  because they're outside the verified `Program` they wrap; this keeps
  `emitInstr` total over `Instr` without forcing the convention into the
  verified core.
-/

namespace EvmAsm.Codegen

/-- Halt convention selected at codegen time. -/
inductive HaltConv where
  | sp1
  | linux93
  deriving DecidableEq, Repr

namespace HaltConv

def ofString? : String → Option HaltConv
  | "sp1"     => some .sp1
  | "linux93" => some .linux93
  | _         => none

def toString : HaltConv → String
  | .sp1     => "sp1"
  | .linux93 => "linux93"

instance : ToString HaltConv := ⟨HaltConv.toString⟩

end HaltConv

/-- Inclusive lower bound of the verified valid memory region.
    Mirrors `MEM_START` at `EvmAsm/Rv64/Basic.lean:244`. -/
def MEM_START : Nat := 0x20

/-- Inclusive upper bound of the verified valid memory region.
    Mirrors `MEM_END` at `EvmAsm/Rv64/Basic.lean:247`. -/
def MEM_END : Nat := 0x78000000

/-- Halt stub emitted *after* the verified body. -/
def emitHaltStub : HaltConv → String
  | .sp1 =>
      "  li x5, 0\n" ++
      "  ecall"
  | .linux93 =>
      "  li x17, 93\n" ++
      "  li x10, 0\n" ++
      "  ecall"

/-- Header preamble: disable RVC so every encoding is a 4-byte instruction
    (predictable PC arithmetic; required for the future binary encoder). -/
def textPreamble : String :=
  ".option norvc\n" ++
  ".section .text\n" ++
  ".globl _start\n" ++
  "_start:"

/-- Wrap an emitted program body in the M0 program template. -/
def emitTextUnit (hc : HaltConv) (body : String) : String :=
  String.intercalate "\n"
    [ textPreamble
    , body
    , emitHaltStub hc
    , ""
    ]

end EvmAsm.Codegen
