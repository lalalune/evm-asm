/-
  EvmAsm.Codegen.Programs.ExpProperty

  Property-test harness for the EXP opcode (`evm_exp_from_input`).

  Lifted out of `Programs/Evm.lean` to stay within the file-size cap
  (see `Programs.lean` §File-size guard). Uses the EXP body defined in
  `EvmAsm.Evm64.Exp.Program` and the callable MUL shim from
  `EvmAsm.Evm64.Multiply.Callable`.

  NOTE: The current EXP implementation has a known bug — `mul_callable`
  clobbers x6, which the EXP loop uses as its per-limb bit counter (init
  64, decremented per bit, resets at limb boundaries). Random property
  testing via `scripts/codegen-evm_exp-property-check.sh` will surface
  wrong results for non-trivial inputs, guiding development of the
  corrected `_fixed_fixed` variant that uses callee-saved registers for
  the limb counter and limb pointer.
-/

import EvmAsm.Codegen.Programs.Evm
import EvmAsm.Evm64.Exp.Program
import EvmAsm.Evm64.Multiply.Callable

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## evm_exp_from_input — property-test harness

    Standalone EXP computation using prover-supplied operands. Same
    input/output conventions as `evm_div_from_input`:
    - ziskemu `-i <file>` payload: 8-byte LE length (= 64) followed by
      32 bytes of base (LE limbs) and 32 bytes of exponent (LE limbs).
    - First 32 bytes of `OUTPUT_ADDR`: the LE result base^exp mod 2^256.

    Memory layout:
      x2  → exp_sp_scratch : 32 B (result accumulator at sp+0..31)
      x12 → operands_ram   : 128 B
                              +0..31  base
                              +32..63 exponent (overwritten by result)
                              +64..127 mul_callable scratch frame

    JAL offsets use canonical values from `Program.lean`:
      squaringMulOff = 196, condMulOff = 88.
    Both target `mul_callable` placed immediately after the 84-instruction
    (336-byte) EXP body. -/

def evm_exp_from_input : Program :=
  LI .x5 (INPUT_ADDR + (BitVec.ofNat 64 INPUT_DATA_OFFSET)) ;;
  copy64 .x12 .x5 .x6 ++
  EvmAsm.Evm64.evm_exp_msb_saved_bit_two_mul_fixed_canonical
    EvmAsm.Evm64.canonicalExpSquaringMulOff
    EvmAsm.Evm64.canonicalExpCondMulOff ++
  EvmAsm.Evm64.mul_callable ++
  evmAddEpilogue

def evmExpFromInputPrologue : String :=
  "  la x2, exp_sp_scratch\n" ++
  "  la x12, operands_ram"

def evmExpFromInputDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "exp_sp_scratch:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "operands_ram:\n" ++
  "  .zero 128"

def evmExpFromInputUnit : BuildUnit := {
  body        := evm_exp_from_input
  prologueAsm := evmExpFromInputPrologue
  dataAsm     := evmExpFromInputDataSection
}

end EvmAsm.Codegen
