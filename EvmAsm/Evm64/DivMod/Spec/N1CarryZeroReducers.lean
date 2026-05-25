import EvmAsm.Evm64.DivMod.Spec.N1QuotientStackBridge
import EvmAsm.Evm64.DivMod.Spec.CallSkipOverestimateBridge

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmWord (val256)

/-- First n=1 step carry-zero reducer. For the call branch, the step starts
    with top limb zero, so proving the `mulsubN4` carry `c3` is zero is enough
    to discharge `fullDivN1R3CarryZero`. -/
theorem fullDivN1R3CarryZero_true_of_mulsub_c3_zero
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hc3 :
      mulsubN4_c3
        (div128Quot
          (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
          (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
          (fullDivN1NormV b0 b1 b2 b3).1)
        (fullDivN1NormV b0 b1 b2 b3).1
        (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.2
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
        (0 : Word)
        (0 : Word) = 0) :
    fullDivN1R3CarryZero true a0 a1 a2 a3 b0 b1 b2 b3 := by
  unfold fullDivN1R3CarryZero fullDivN1R3
  exact iterN1_true_carry_zero_of_mulsub_c3_zero
    (fullDivN1NormV b0 b1 b2 b3).1
    (fullDivN1NormV b0 b1 b2 b3).2.1
    (fullDivN1NormV b0 b1 b2 b3).2.2.1
    (fullDivN1NormV b0 b1 b2 b3).2.2.2
    (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
    (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
    (0 : Word)
    (0 : Word)
    (0 : Word)
    hc3 rfl

/-- Product-bound form of the first n=1 step carry-zero reducer. This composes
    the generic `mulsubN4_c3` inequality bridge with the R3 reducer above, so
    later arithmetic only needs to prove that the selected trial quotient times
    the normalized n=1 divisor is bounded by the first partial dividend. -/
theorem fullDivN1R3CarryZero_true_of_qHat_mul_le
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (h_mul_le :
      (div128Quot
          (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
          (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
          (fullDivN1NormV b0 b1 b2 b3).1).toNat *
        val256
          (fullDivN1NormV b0 b1 b2 b3).1
          (fullDivN1NormV b0 b1 b2 b3).2.1
          (fullDivN1NormV b0 b1 b2 b3).2.2.1
          (fullDivN1NormV b0 b1 b2 b3).2.2.2 ≤
        val256
          (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
          (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
          (0 : Word)
          (0 : Word)) :
    fullDivN1R3CarryZero true a0 a1 a2 a3 b0 b1 b2 b3 := by
  apply fullDivN1R3CarryZero_true_of_mulsub_c3_zero
  exact c3_un_zero_of_qHat_mul_le (qHat :=
    div128Quot
      (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
      (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
      (fullDivN1NormV b0 b1 b2 b3).1) h_mul_le

/-- 128/64-bound form of the first n=1 step carry-zero reducer. When the
    normalized divisor is one-limb, the generic product bound for R3 is exactly
    the usual `qHat * v0 ≤ uHi * 2^64 + uLo` obligation. -/
theorem fullDivN1R3CarryZero_true_of_qHat_v0_mul_le
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hv1z : (fullDivN1NormV b0 b1 b2 b3).2.1 = 0)
    (hv2z : (fullDivN1NormV b0 b1 b2 b3).2.2.1 = 0)
    (hv3z : (fullDivN1NormV b0 b1 b2 b3).2.2.2 = 0)
    (h_qHat_mul_le :
      (div128Quot
          (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
          (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
          (fullDivN1NormV b0 b1 b2 b3).1).toNat *
        (fullDivN1NormV b0 b1 b2 b3).1.toNat ≤
      (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2.toNat * 2^64 +
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1.toNat) :
    fullDivN1R3CarryZero true a0 a1 a2 a3 b0 b1 b2 b3 := by
  apply fullDivN1R3CarryZero_true_of_qHat_mul_le
  rw [hv1z, hv2z, hv3z]
  simp [EvmWord.val256]
  omega

end EvmAsm.Evm64
