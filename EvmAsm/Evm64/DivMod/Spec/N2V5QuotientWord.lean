/-
  EvmAsm.Evm64.DivMod.Spec.N2V5QuotientWord

  The v5 n=2 quotient word and its per-limb extraction: `fromLimbs` of the three
  v5 n=2 schoolbook digits `fullDivN2R{0,1,2}V5.1` (top limb 0, since n=2 ⇒
  b2=b3=0 ⇒ quotient < 2^192).  v5 counterpart of `fullDivN2QuotientWord`
  (N2QuotientWord.lean); the per-limb facts feed the v5 n=2 quotient-correctness
  and lane post bridge.  Bead `evm-asm-wbc4i.9.2`.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN2V5Families

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmWord

/-- Pack the three per-limb v5 n=2 DIV results into a single `EvmWord` (top
    limb `0`). -/
@[irreducible]
def fullDivN2QuotientWordV5 (bltu_2 bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : EvmWord :=
  EvmWord.fromLimbs (fun i : Fin 4 =>
    match i with
    | 0 => (fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1
    | 1 => (fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1
    | 2 => (fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1
    | 3 => (0 : Word))

theorem fullDivN2QuotientWordV5_getLimbN0 (bltu_2 bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    (fullDivN2QuotientWordV5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).getLimbN 0
    = (fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1 := by
  delta fullDivN2QuotientWordV5; exact EvmWord.getLimbN_fromLimbs_0

theorem fullDivN2QuotientWordV5_getLimbN1 (bltu_2 bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    (fullDivN2QuotientWordV5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).getLimbN 1
    = (fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1 := by
  delta fullDivN2QuotientWordV5; exact EvmWord.getLimbN_fromLimbs_1

theorem fullDivN2QuotientWordV5_getLimbN2 (bltu_2 bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    (fullDivN2QuotientWordV5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).getLimbN 2
    = (fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1 := by
  delta fullDivN2QuotientWordV5; exact EvmWord.getLimbN_fromLimbs_2

theorem fullDivN2QuotientWordV5_getLimbN3 (bltu_2 bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    (fullDivN2QuotientWordV5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).getLimbN 3
    = (0 : Word) := by
  delta fullDivN2QuotientWordV5; exact EvmWord.getLimbN_fromLimbs_3

end EvmAsm.Evm64
