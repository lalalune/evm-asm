/-
  EvmAsm.Evm64.DivMod.LoopIterN1.LoopQuotDivV5

  The v5 n=1 loop's assembled quotient — with the top digit expressed in the loop
  form `iterN1Call_v5` (as the loop post actually stores it) instead of the
  schoolbook `fullDivN1R3V5 true` — equals the true division `EvmWord.div a b`,
  from the divisor shape.  A thin restatement of
  `fullDivN1QuotientWordV5_eq_div_of_shape` through the digit-3 bridge (#7282),
  giving the lane wrapper the quotient-correctness fact in the loop's vocabulary.
  Bead `evm-asm-wbc4i.9.1`.
-/

import EvmAsm.Evm64.DivMod.LoopIterN1.LoopAtShapeBridgeV5
import EvmAsm.Evm64.DivMod.Spec.N1V5Quotient

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- The four v5 n=1 loop quotient digits — top digit in loop form `iterN1Call_v5`
    over the normalized top window — assemble to `EvmWord.div a b`. -/
theorem fullDivN1Quotient_loopform_eq_div_of_shape
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0) :
    EvmWord.fromLimbs (fun i : Fin 4 => match i with
      | 0 => (fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3).1
      | 1 => (fullDivN1R1V5 true true true a0 a1 a2 a3 b0 b1 b2 b3).1
      | 2 => (fullDivN1R2V5 true true a0 a1 a2 a3 b0 b1 b2 b3).1
      | 3 => (iterN1Call_v5 (fullDivN1NormV b0 b1 b2 b3).1 (fullDivN1NormV b0 b1 b2 b3).2.1
                (fullDivN1NormV b0 b1 b2 b3).2.2.1 (fullDivN1NormV b0 b1 b2 b3).2.2.2
                (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1 (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
                0 0 0).1)
    = EvmWord.div
        (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3)
        (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3) := by
  rw [← fullDivN1R3V5_eq_iterN1Call_v5]
  exact fullDivN1QuotientWordV5_eq_div_of_shape a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hshift_nz

end EvmAsm.Evm64
