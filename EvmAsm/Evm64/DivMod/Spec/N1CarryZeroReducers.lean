import EvmAsm.Evm64.DivMod.Spec.N1QuotientStackBridge
import EvmAsm.Evm64.DivMod.Spec.CallSkipOverestimateBridge
import EvmAsm.Evm64.EvmWordArith.KnuthTheoremB

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

/-- When the n=1 CLZ shift is nonzero, the anti-shift spill from the low
    divisor limb into normalized limb 1 is zero. -/
theorem fullDivN1AntiShift_spill_zero_of_shift_nz
    (b0 : Word)
    (hshift_nz : (clzResult b0).1 ≠ 0) :
    b0 >>> ((fullDivN1AntiShift b0).toNat % 64) = 0 := by
  have h_shift_pos : 1 ≤ (clzResult b0).1.toNat := by
    rcases Nat.eq_zero_or_pos (clzResult b0).1.toNat with h | h
    · exfalso
      apply hshift_nz
      exact BitVec.eq_of_toNat_eq (by simp [h])
    · exact h
  have hshift_le : (clzResult b0).1.toNat ≤ 63 := clzResult_fst_toNat_le b0
  have hanti :
      (fullDivN1AntiShift b0).toNat % 64 = 64 - (clzResult b0).1.toNat := by
    unfold fullDivN1AntiShift fullDivN1Shift
    exact antiShift_toNat_mod_eq h_shift_pos hshift_le
  rw [hanti]
  exact (ushiftRight_eq_zero_iff (64 - (clzResult b0).1.toNat)).mpr
    (clzResult_fst_top_bound b0)

/-- Under the runtime n=1 divisor shape and a nonzero normalization shift,
    normalized divisor limb 1 is zero. -/
theorem fullDivN1NormV_limb1_eq_zero_of_shape_shift_nz
    (b0 b1 b2 b3 : Word)
    (hb1z : b1 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0) :
    (fullDivN1NormV b0 b1 b2 b3).2.1 = 0 := by
  rw [fullDivN1NormV_limb1_eq_of_shape b0 b1 b2 b3 hb1z]
  exact fullDivN1AntiShift_spill_zero_of_shift_nz b0 hshift_nz

/-- Runtime n=1 divisor-shape form of the first-step carry-zero reducer. This
    leaves only the standard 128/64 product bound for the selected trial
    quotient. -/
theorem fullDivN1R3CarryZero_true_of_shape_qHat_v0_mul_le
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0)
    (h_qHat_mul_le :
      (div128Quot
          (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
          (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
          (fullDivN1NormV b0 b1 b2 b3).1).toNat *
        (fullDivN1NormV b0 b1 b2 b3).1.toNat ≤
      (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2.toNat * 2^64 +
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1.toNat) :
    fullDivN1R3CarryZero true a0 a1 a2 a3 b0 b1 b2 b3 := by
  exact fullDivN1R3CarryZero_true_of_qHat_v0_mul_le
    a0 a1 a2 a3 b0 b1 b2 b3
    (fullDivN1NormV_limb1_eq_zero_of_shape_shift_nz b0 b1 b2 b3 hb1z hshift_nz)
    (fullDivN1NormV_limb2_eq_zero_of_shape b0 b1 b2 b3 hb1z hb2z)
    (fullDivN1NormV_limb3_eq_zero_of_shape b0 b1 b2 b3 hb2z hb3z)
    h_qHat_mul_le

/-- Exact-floor form of the first-step n=1 carry-zero reducer. Once the
    selected `div128Quot` is identified with the usual 128/64 Nat quotient,
    the product bound follows from `Nat.div_mul_le_self`. -/
theorem fullDivN1R3CarryZero_true_of_shape_div128Quot_floor
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0)
    (h_qHat_eq :
      (div128Quot
          (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
          (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
          (fullDivN1NormV b0 b1 b2 b3).1).toNat =
        ((fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2.toNat * 2^64 +
          (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1.toNat) /
          (fullDivN1NormV b0 b1 b2 b3).1.toNat) :
    fullDivN1R3CarryZero true a0 a1 a2 a3 b0 b1 b2 b3 := by
  apply fullDivN1R3CarryZero_true_of_shape_qHat_v0_mul_le
    a0 a1 a2 a3 b0 b1 b2 b3 hb1z hb2z hb3z hshift_nz
  rw [h_qHat_eq]
  exact Nat.div_mul_le_self
    ((fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2.toNat * 2^64 +
      (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1.toNat)
    (fullDivN1NormV b0 b1 b2 b3).1.toNat

/-- The first n=1 128/64 trial call is in the strict call regime. A positive
    normalization shift makes the overflow limb of the normalized dividend
    below `2^63`, while the normalized divisor limb is at least `2^63`. -/
theorem fullDivN1NormU_top_lt_normV_limb0_of_b0_ne_zero_shift_nz
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hb0nz : b0 ≠ 0)
    (hshift_nz : (clzResult b0).1 ≠ 0) :
    (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2.toNat <
      (fullDivN1NormV b0 b1 b2 b3).1.toNat := by
  have h_shift_pos : 1 ≤ (clzResult b0).1.toNat := by
    rcases Nat.eq_zero_or_pos (clzResult b0).1.toNat with h | h
    · exfalso
      apply hshift_nz
      exact BitVec.eq_of_toNat_eq (by simp [h])
    · exact h
  have h_u4_lt_pow63 :
      (a3 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b0).1).toNat % 64)).toNat <
        2^63 :=
    u_top_lt_pow63_of_shift_nz a3 (clzResult b0).1 h_shift_pos
      (clzResult_fst_toNat_le b0)
  have h_b0_ge_pow63 :
      (b0 <<< ((clzResult b0).1.toNat % 64)).toNat ≥ 2^63 :=
    b3_shifted_ge_pow63 hb0nz
  have h_lt := Nat.lt_of_lt_of_le h_u4_lt_pow63 h_b0_ge_pow63
  simpa [fullDivN1NormU, fullDivN1NormV, fullDivN1Shift, fullDivN1AntiShift]
    using h_lt

/-- Runtime n=1 divisor-shape wrapper for the strict first-call regime. -/
theorem fullDivN1NormU_top_lt_normV_limb0_of_shape_shift_nz
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0) :
    (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2.toNat <
      (fullDivN1NormV b0 b1 b2 b3).1.toNat := by
  exact fullDivN1NormU_top_lt_normV_limb0_of_b0_ne_zero_shift_nz
    a0 a1 a2 a3 b0 b1 b2 b3
    (fullDivN1_b0_ne_zero_of_shape b0 b1 b2 b3 hbnz hb1z hb2z hb3z)
    hshift_nz

end EvmAsm.Evm64
