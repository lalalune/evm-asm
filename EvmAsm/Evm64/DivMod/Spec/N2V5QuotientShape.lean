/-
  EvmAsm.Evm64.DivMod.Spec.N2V5QuotientShape

  **v5 n=2 quotient correctness from shape (shift≠0):**
  `fullDivN2QuotientWordV5 = EvmWord.div a b`.

  Combines the accumulated-quotient correctness `fullDivN2_acc_quot_eq_div_of_shape`
  (N2V5NormScaled — the cross-digit telescope) with the EvmWord lift
  `div_of_val256_eq_div`: the assembled quotient word's `val256` equals
  `val256 a / val256 b`, hence the word equals `EvmWord.div a b`.

  This is the n=2 analog of `fullDivN1QuotientWordV5_eq_div_of_shape`
  (N1V5Quotient), and the central correctness statement the n=2 lane wrapper
  consumes (after discharging the `bltu` path matches from `isTrialN2V5_j*`).
  Bead `evm-asm-wbc4i.9.2`.
-/

import EvmAsm.Evm64.DivMod.Spec.N2V5NormScaled
import EvmAsm.Evm64.DivMod.Spec.N2V5QuotientWord
import EvmAsm.Evm64.DivMod.Spec.N2QuotientWord

namespace EvmAsm.Evm64

open EvmWord EvmAsm.Rv64

/-- **v5 n=2 quotient correctness (shift≠0), from shape + `bltu` path matches.**
    The assembled v5 n=2 quotient word equals `EvmWord.div a b`. -/
theorem fullDivN2QuotientWordV5_eq_div_of_shape
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) (bltu_2 bltu_1 bltu_0 : Bool)
    (hb2z : b2 = 0) (hb3z : b3 = 0) (hshift_nz : (clzResult b1).1 ≠ 0) (hb1nz : b1 ≠ 0)
    (hc2 : bltu_2 = true → BitVec.ult (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2 (fullDivN2NormV b0 b1 b2 b3).2.1 = true)
    (hm2 : bltu_2 = false → ¬ BitVec.ult (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2 (fullDivN2NormV b0 b1 b2 b3).2.1)
    (hc1 : bltu_1 = true → BitVec.ult (fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 (fullDivN2NormV b0 b1 b2 b3).2.1 = true)
    (hm1 : bltu_1 = false → ¬ BitVec.ult (fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 (fullDivN2NormV b0 b1 b2 b3).2.1)
    (hc0 : bltu_0 = true → BitVec.ult (fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 (fullDivN2NormV b0 b1 b2 b3).2.1 = true)
    (hm0 : bltu_0 = false → ¬ BitVec.ult (fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 (fullDivN2NormV b0 b1 b2 b3).2.1) :
    fullDivN2QuotientWordV5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3 =
      EvmWord.div
        (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3)
        (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3) := by
  have h0 : (0:Word).toNat = 0 := rfl
  have hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0 := by
    intro h
    have h2 := (BitVec.or_eq_zero_iff.mp h).1
    have h3 := (BitVec.or_eq_zero_iff.mp h2).1
    exact hb1nz (BitVec.or_eq_zero_iff.mp h3).2
  have hacc := fullDivN2_acc_quot_eq_div_of_shape a0 a1 a2 a3 b0 b1 b2 b3
    bltu_2 bltu_1 bltu_0 hb2z hb3z hshift_nz hb1nz hc2 hm2 hc1 hm1 hc0 hm0
  have hqval : val256 (fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1
      (fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1
      (fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1 0
      = val256 a0 a1 a2 a3 / val256 b0 b1 b2 b3 := by
    rw [← hacc]; simp only [EvmWord.val256, h0]; ring
  have hdiv := div_of_val256_eq_div hbnz hqval
  unfold fullDivN2QuotientWordV5
  exact hdiv

end EvmAsm.Evm64
