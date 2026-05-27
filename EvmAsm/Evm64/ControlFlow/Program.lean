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

  ## Known limitation (M15)

  These bodies do NOT validate that `dest` lands on a JUMPDEST byte
  (`code[dest] == 0x5b`). A spec-compliant EVM rejects invalid jumps;
  ours unconditionally follows them. The follow-on PR (M15.5 / M16)
  will add the inline `LBU + BEQ 0x5b` check. For now we trust the
  program — the codegen-side test cases all jump to real JUMPDEST
  bytes.

  Slice planned under M15 of `CODEGEN.md`.
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
    `destReg` is a caller-saved temporary distinct from `x0`, `x10`,
    `x12`, `codeBaseReg`. 3 instructions = 12 bytes.

    Upper 3 limbs of the popped word are ignored (assumes `dest <
    2^64`, which holds for any realistic EVM bytecode). -/
def evm_jump (codeBaseReg destReg : Reg) : Program :=
  LD destReg .x12 0 ;;
  ADDI .x12 .x12 32 ;;
  ADD .x10 codeBaseReg destReg

/-- Parameterized RISC-V program implementing `JUMPI` (0x57).
    Pops `dest` (top of stack) and `cond` (second). If `cond` is
    nonzero (any limb has any bit set), updates
    `x10 := codeBaseReg + dest`. Otherwise advances `x10` by 1
    (fall-through).

    `destReg`, `condReg`, `tmpReg` are pairwise distinct caller-saved
    temporaries, also distinct from `x0`, `x10`, `x12`, `codeBaseReg`.
    13 instructions = 52 bytes.

    Branch offsets:
    - `BEQ condReg x0 12` skips ADD + JAL (2 instructions, 8 bytes)
      → lands at the fall-through ADDI.
    - `JAL x0 8` skips ADDI (1 instruction, 4 bytes) → lands just
      past the body (the handler's `ret` tail). -/
def evm_jumpi (codeBaseReg destReg condReg tmpReg : Reg) : Program :=
  LD destReg .x12 0 ;;
  LD condReg .x12 32 ;;
  LD tmpReg .x12 40 ;;
  OR' condReg condReg tmpReg ;;
  LD tmpReg .x12 48 ;;
  OR' condReg condReg tmpReg ;;
  LD tmpReg .x12 56 ;;
  OR' condReg condReg tmpReg ;;
  ADDI .x12 .x12 64 ;;
  BEQ condReg .x0 (BitVec.ofNat 13 12) ;;
  ADD .x10 codeBaseReg destReg ;;
  JAL .x0 (BitVec.ofNat 21 8) ;;
  ADDI .x10 .x10 1

end ControlFlow
end EvmAsm.Evm64
