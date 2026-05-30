/-
  EvmAsm.Evm64.DivMod.Spec.N2V5R2Conservation

  Top-digit (j=2) conservation for the v5 n=2 schoolbook, call path: connects the
  generic per-digit conservation `iterN2V5_true_conservation` to the concrete
  `fullDivN2R2V5 true` digit (whose call inputs are the normalized-divisor top
  window `u.2.2.1 / u.2.2.2.1 / u.2.2.2.2` over `v`).  First link of the chained
  `fullDivN2MulSubEqV5`.  Bead `evm-asm-wbc4i.9.2`.
-/

import EvmAsm.Evm64.DivMod.Spec.N2V5DigitConservation

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmWord

theorem fullDivN2R2V5_conservation (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hbnz : (fullDivN2NormV b0 b1 b2 b3).1 ||| (fullDivN2NormV b0 b1 b2 b3).2.1 |||
        (fullDivN2NormV b0 b1 b2 b3).2.2.1 ||| (fullDivN2NormV b0 b1 b2 b3).2.2.2 ≠ 0)
    (hc3_one_of_borrow :
      BitVec.ult (0 : Word)
          (mulsubN4
            (divKTrialCallV5QHat (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2
              (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1 (fullDivN2NormV b0 b1 b2 b3).2.1)
            (fullDivN2NormV b0 b1 b2 b3).1 (fullDivN2NormV b0 b1 b2 b3).2.1
            (fullDivN2NormV b0 b1 b2 b3).2.2.1 (fullDivN2NormV b0 b1 b2 b3).2.2.2
            (fullDivN2NormU a0 a1 a2 a3 b1).2.2.1 (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1
            (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2 (0 : Word)).2.2.2.2 →
        (mulsubN4
            (divKTrialCallV5QHat (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2
              (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1 (fullDivN2NormV b0 b1 b2 b3).2.1)
            (fullDivN2NormV b0 b1 b2 b3).1 (fullDivN2NormV b0 b1 b2 b3).2.1
            (fullDivN2NormV b0 b1 b2 b3).2.2.1 (fullDivN2NormV b0 b1 b2 b3).2.2.2
            (fullDivN2NormU a0 a1 a2 a3 b1).2.2.1 (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1
            (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2 (0 : Word)).2.2.2.2 = 1)
    (hcarry2 :
      isAddbackCarry2Nz
        (divKTrialCallV5QHat (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2
          (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1 (fullDivN2NormV b0 b1 b2 b3).2.1)
        (fullDivN2NormV b0 b1 b2 b3).1 (fullDivN2NormV b0 b1 b2 b3).2.1
        (fullDivN2NormV b0 b1 b2 b3).2.2.1 (fullDivN2NormV b0 b1 b2 b3).2.2.2
        (fullDivN2NormU a0 a1 a2 a3 b1).2.2.1 (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1
        (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2 (0 : Word) (0 : Word)) :
    val256 (fullDivN2NormU a0 a1 a2 a3 b1).2.2.1
        (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1 (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2 0
      + (0 : Word).toNat * 2^256 =
      (fullDivN2R2V5 true a0 a1 a2 a3 b0 b1 b2 b3).1.toNat *
        val256 (fullDivN2NormV b0 b1 b2 b3).1 (fullDivN2NormV b0 b1 b2 b3).2.1
          (fullDivN2NormV b0 b1 b2 b3).2.2.1 (fullDivN2NormV b0 b1 b2 b3).2.2.2 +
      val256
        (fullDivN2R2V5 true a0 a1 a2 a3 b0 b1 b2 b3).2.1
        (fullDivN2R2V5 true a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
        (fullDivN2R2V5 true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
        (fullDivN2R2V5 true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 +
      (fullDivN2R2V5 true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.2.toNat * 2^256 := by
  unfold fullDivN2R2V5
  exact iterN2V5_true_conservation
    (fullDivN2NormV b0 b1 b2 b3).1 (fullDivN2NormV b0 b1 b2 b3).2.1
    (fullDivN2NormV b0 b1 b2 b3).2.2.1 (fullDivN2NormV b0 b1 b2 b3).2.2.2
    (fullDivN2NormU a0 a1 a2 a3 b1).2.2.1 (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1
    (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2 (0 : Word) (0 : Word)
    hbnz hc3_one_of_borrow hcarry2

end EvmAsm.Evm64
