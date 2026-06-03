/-
  EvmAsm.Evm64.ControlFlow.Program

  RISC-V programs implementing the EVM control-flow opcodes
  `PC` (0x58), `JUMP` (0x56), and `JUMPI` (0x57).

  These are the next-tier control-flow primitives on top of `JUMPDEST`
  (0x5b, a no-op marker, wired in M14). All three bodies are parametric
  in registers; the M15 codegen wiring sets:

  - `codeBaseReg = .x21` — initialised in the dispatcher prologue to
    the start of the EVM bytecode region (preserved across handlers).
  - scratch `destReg` / `condReg` / `tmpReg` from the M7 / M12 scratch
    pool (`x14` / `x15` / `x16`).

  ## Semantics

  - **PC** pushes the byte offset of the PC opcode itself within the
    bytecode. In the dispatcher's frame, that's `x10 - codeBaseReg`
    at handler entry (the dispatcher's `jalr` lands here with `x10`
    still pointing AT the PC byte).
  - **JUMP** pops `dest` (low 64 bits of the 256-bit top word) and
    sets `x10 := codeBaseReg + dest`. The dispatcher loop's next
    `lbu x5, 0(x10)` reads the jump-target byte.
  - **JUMPI** pops `dest` (top) and `cond` (next). If `cond` is
    nonzero (any bit in any of the 4 limbs set), behaves like JUMP.
    Otherwise advances `x10` by 1 (the JUMPI opcode is 1 byte).

  ## JUMPDEST-validity (M15.5, Level 1)

  `JUMP` / `JUMPI` now load `code[dest]` into `validityReg` (the
  conditional-jump *taken* path of `JUMPI` does the load; the
  *not-taken* path writes the sentinel `0x5b` so the same downstream
  check is a no-op). The codegen handler tail compares `validityReg`
  to `0x5b` and routes a mismatch to the dispatcher's exceptional-halt
  path (`.exit_invalid`). Keeping only the byte *load* here (not the
  branch-to-halt, which needs a host-specific label) lets the stateless
  guest VM reuse these bodies with its own halt routing.

  ### Remaining gap (Level 2)

  This is a byte check, not a full JUMPDEST-validity analysis: a `0x5b`
  byte that sits inside PUSH immediate data is *not* a legal jump target
  but passes this check. Full compliance needs a valid-jumpdest bitmap
  built by scanning the bytecode (accounting for PUSH1–32 operands) at
  dispatch entry — a separate, larger slice. Level 1 already eliminates
  the dangerous "follow garbage past the bytecode into `.data`" cases.

  Slice planned under M15.5 of `CODEGEN.md`.
-/

import EvmAsm.Rv64.Program

namespace EvmAsm.Evm64
namespace ControlFlow

open EvmAsm.Rv64

/-- Parameterized RISC-V program implementing `PC` (0x58).
    Pushes the byte offset of the PC opcode itself within the EVM
    bytecode. Computes `pc = x10 - codeBaseReg` at handler entry.
    `tmpReg` must be distinct from `x0`, `x10`, `x12`, `codeBaseReg`.
    6 instructions = 24 bytes. -/
def evm_pc (codeBaseReg tmpReg : Reg) : Program :=
  SUB tmpReg .x10 codeBaseReg ;;
  ADDI .x12 .x12 (-32) ;;
  SD .x12 tmpReg 0 ;;
  SD .x12 .x0 8 ;;
  SD .x12 .x0 16 ;;
  SD .x12 .x0 24

/-- Parameterized RISC-V program implementing `JUMP` (0x56).
    Pops the destination from the EVM stack (low 64 bits of the top
    256-bit word) and updates `x10 := codeBaseReg + dest`. The
    dispatcher loop resumes at the new PC.
    `destReg` / `validityReg` are caller-saved temporaries distinct from
    `x0`, `x10`, `x12`, `codeBaseReg` (and each other). 4 instructions
    = 16 bytes.

    The trailing `LBU validityReg, 0(x10)` loads `code[dest]` for the
    JUMPDEST-validity check; the handler tail compares it to `0x5b`.

    Upper 3 limbs of the popped word are ignored (assumes `dest <
    2^64`, which holds for any realistic EVM bytecode). -/
def evm_jump (codeBaseReg destReg validityReg : Reg) : Program :=
  LD destReg .x12 0 ;;
  ADDI .x12 .x12 32 ;;
  ADD .x10 codeBaseReg destReg ;;
  LBU validityReg .x10 0

/-- Parameterized RISC-V program implementing `JUMPI` (0x57).
    Pops `dest` (top of stack) and `cond` (second). If `cond` is
    nonzero (any limb has any bit set), updates
    `x10 := codeBaseReg + dest`. Otherwise advances `x10` by 1
    (fall-through).

    `destReg`, `condReg`, `tmpReg`, `validityReg` are pairwise distinct
    caller-saved temporaries, also distinct from `x0`, `x10`, `x12`,
    `codeBaseReg`. 15 instructions = 60 bytes.

    JUMPDEST-validity: the *taken* path loads `code[dest]` into
    `validityReg`; the *not-taken* path writes the sentinel `0x5b` so
    the handler tail's `validityReg == 0x5b` check is a no-op for
    fall-through. The handler tail does the compare + halt routing.

    Branch offsets (re-pinned for the two extra instructions):
    - `BEQ condReg x0 16` skips ADD + LBU + JAL (3 instructions,
      12 bytes) → lands at the fall-through `ADDI x10`.
    - `JAL x0 12` skips the two not-taken instrs (`ADDI x10` +
      `ADDI validityReg`, 8 bytes) → lands just past the body (the
      handler's tail). -/
def evm_jumpi (codeBaseReg destReg condReg tmpReg validityReg : Reg) : Program :=
  LD destReg .x12 0 ;;
  LD condReg .x12 32 ;;
  LD tmpReg .x12 40 ;;
  OR' condReg condReg tmpReg ;;
  LD tmpReg .x12 48 ;;
  OR' condReg condReg tmpReg ;;
  LD tmpReg .x12 56 ;;
  OR' condReg condReg tmpReg ;;
  ADDI .x12 .x12 64 ;;
  BEQ condReg .x0 (BitVec.ofNat 13 16) ;;
  ADD .x10 codeBaseReg destReg ;;
  LBU validityReg .x10 0 ;;
  JAL .x0 (BitVec.ofNat 21 12) ;;
  ADDI .x10 .x10 1 ;;
  ADDI validityReg .x0 (BitVec.ofNat 12 0x5b)

end ControlFlow
end EvmAsm.Evm64
