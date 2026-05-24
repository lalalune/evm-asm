/-
  EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV4.QuotientBounds

  Word-to-Nat bridge wrappers for the v4 trial-call quotient digits.
  These keep downstream exact-quotient proofs phrased in terms of the
  source-of-truth `divKTrialCallV4*` definitions while reusing the generic
  Knuth lower-bound lemmas.
-/

import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV4.Algorithm
import EvmAsm.Evm64.EvmWordArith.Div128KnuthLower
import EvmAsm.Evm64.EvmWordArith.Div128FinalAssembly
import EvmAsm.Evm64.DivMod.LoopBody.TrialCallBounds

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- The v4 trial-call low half-word `un0` is always below `2^32`. -/
theorem divKTrialCallV4Un0_lt_pow32 (uLo : Word) :
    (divKTrialCallV4Un0 uLo).toNat < 2^32 := by
  rw [divKTrialCallV4Un0_eq]
  rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
  have h_shl : (uLo <<< (32 : BitVec 6).toNat : Word).toNat < 2^64 :=
    (uLo <<< (32 : BitVec 6).toNat : Word).isLt
  exact Nat.div_lt_of_lt_mul (by omega)

/-- Phase 2 first-correction lower bound, wrapped for the v4 trial-call
    definitions.

    This is the v4 analogue of `algorithmQ0Prime_ge_q_true_0`: under
    `un21 < dHi * 2^32`, the first-corrected second quotient digit `Q0d`
    is at least the true second Knuth digit. -/
theorem divKTrialCallV4Q0d_ge_q_true_0_of_un21_lt_dHi_mul_pow32
    (uHi uLo vTop : Word)
    (hdHi_ge : (divKTrialCallV4DHi vTop).toNat ≥ 2^31)
    (hdHi_lt : (divKTrialCallV4DHi vTop).toNat < 2^32)
    (hdLo_lt : (divKTrialCallV4DLo vTop).toNat < 2^32)
    (hUn21_lt_dHi_pow32 :
      (divKTrialCallV4Un21 uHi uLo vTop).toNat <
        (divKTrialCallV4DHi vTop).toNat * 2^32)
    (hUn21_lt_vTop :
      (divKTrialCallV4Un21 uHi uLo vTop).toNat <
        (divKTrialCallV4DHi vTop).toNat * 2^32 +
          (divKTrialCallV4DLo vTop).toNat) :
    ((divKTrialCallV4Un21 uHi uLo vTop).toNat * 2^32 +
        (divKTrialCallV4Un0 uLo).toNat) /
      ((divKTrialCallV4DHi vTop).toNat * 2^32 +
        (divKTrialCallV4DLo vTop).toNat) ≤
    (divKTrialCallV4Q0d uHi uLo vTop).toNat := by
  unfold divKTrialCallV4Q0d divKTrialCallV4Q0c divKTrialCallV4Rhat2c divKTrialCallV4Un0
  exact
    div128Quot_q0_prime_ge_q_true_0_of_un21_lt_dHi_mul_pow32
      (divKTrialCallV4Un21 uHi uLo vTop)
      (divKTrialCallV4DHi vTop)
      (divKTrialCallV4DLo vTop)
      uLo
      hdHi_ge hdHi_lt hdLo_lt hUn21_lt_dHi_pow32 hUn21_lt_vTop

/-- Phase 2 first-correction lower bound, wrapped for the v4 trial-call
    definitions.

    Variant for the complementary easy hypothesis `un21 < 2^63`, matching
    the generic KB-LB8 theorem. -/
theorem divKTrialCallV4Q0d_ge_q_true_0_of_un21_lt_pow63
    (uHi uLo vTop : Word)
    (hdHi_ge : (divKTrialCallV4DHi vTop).toNat ≥ 2^31)
    (hdHi_lt : (divKTrialCallV4DHi vTop).toNat < 2^32)
    (hdLo_lt : (divKTrialCallV4DLo vTop).toNat < 2^32)
    (hUn21_lt_pow63 : (divKTrialCallV4Un21 uHi uLo vTop).toNat < 2^63)
    (hUn21_lt_vTop :
      (divKTrialCallV4Un21 uHi uLo vTop).toNat <
        (divKTrialCallV4DHi vTop).toNat * 2^32 +
          (divKTrialCallV4DLo vTop).toNat) :
    ((divKTrialCallV4Un21 uHi uLo vTop).toNat * 2^32 +
        (divKTrialCallV4Un0 uLo).toNat) /
      ((divKTrialCallV4DHi vTop).toNat * 2^32 +
        (divKTrialCallV4DLo vTop).toNat) ≤
    (divKTrialCallV4Q0d uHi uLo vTop).toNat := by
  unfold divKTrialCallV4Q0d divKTrialCallV4Q0c divKTrialCallV4Rhat2c divKTrialCallV4Un0
  exact
    div128Quot_q0_prime_ge_q_true_0_of_un21_lt_pow63
      (divKTrialCallV4Un21 uHi uLo vTop)
      (divKTrialCallV4DHi vTop)
      (divKTrialCallV4DLo vTop)
      uLo
      hdHi_ge hdHi_lt hdLo_lt hUn21_lt_pow63 hUn21_lt_vTop

/-- Phase 2 first-correction upper bound, wrapped for the v4 trial-call
    definitions.

    Under `un21 < 2^63`, the first-corrected second quotient digit `Q0d`
    is at most one above the true second Knuth digit. This is the upper
    half paired with `divKTrialCallV4Q0d_ge_q_true_0_of_un21_lt_pow63`;
    together they show `Q0d` is either exact or one high in this range. -/
theorem divKTrialCallV4Q0d_le_q_true_0_plus_one_of_un21_lt_pow63
    (uHi uLo vTop : Word)
    (hdHi_ge : (divKTrialCallV4DHi vTop).toNat ≥ 2^31)
    (hdHi_lt : (divKTrialCallV4DHi vTop).toNat < 2^32)
    (hdLo_lt : (divKTrialCallV4DLo vTop).toNat < 2^32)
    (hUn21_lt_pow63 : (divKTrialCallV4Un21 uHi uLo vTop).toNat < 2^63)
    (hUn21_lt_vTop :
      (divKTrialCallV4Un21 uHi uLo vTop).toNat <
        (divKTrialCallV4DHi vTop).toNat * 2^32 +
          (divKTrialCallV4DLo vTop).toNat) :
    (divKTrialCallV4Q0d uHi uLo vTop).toNat ≤
      ((divKTrialCallV4Un21 uHi uLo vTop).toNat * 2^32 +
          (divKTrialCallV4Un0 uLo).toNat) /
        ((divKTrialCallV4DHi vTop).toNat * 2^32 +
          (divKTrialCallV4DLo vTop).toNat) + 1 := by
  have hdHi_ne : divKTrialCallV4DHi vTop ≠ 0 := by
    intro h_eq
    rw [h_eq] at hdHi_ge
    simp at hdHi_ge
  unfold divKTrialCallV4Q0d divKTrialCallV4Q0c divKTrialCallV4Rhat2c divKTrialCallV4Un0
  unfold div128Quot_phase2b_q0'
  rw [if_pos ?_]
  exact
    div128Quot_q1_prime_le_q_true_1_plus_one
      (divKTrialCallV4Un21 uHi uLo vTop)
      (divKTrialCallV4DHi vTop)
      (divKTrialCallV4DLo vTop)
      (uLo <<< (32 : BitVec 6).toNat)
      hdHi_ne hdHi_ge hdHi_lt hdLo_lt hUn21_lt_vTop hUn21_lt_pow63
  · apply BitVec.eq_of_toNat_eq
    show ((if (rv64_divu (divKTrialCallV4Un21 uHi uLo vTop) (divKTrialCallV4DHi vTop)) >>>
            (32 : BitVec 6).toNat = 0 then
          divKTrialCallV4Un21 uHi uLo vTop -
            rv64_divu (divKTrialCallV4Un21 uHi uLo vTop) (divKTrialCallV4DHi vTop) *
              divKTrialCallV4DHi vTop
        else
          divKTrialCallV4Un21 uHi uLo vTop -
              rv64_divu (divKTrialCallV4Un21 uHi uLo vTop) (divKTrialCallV4DHi vTop) *
                divKTrialCallV4DHi vTop +
            divKTrialCallV4DHi vTop) >>> (32 : BitVec 6).toNat).toNat = (0 : Word).toNat
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    rw [Nat.div_eq_of_lt]
    · rfl
    · exact div128Quot_rhatc_lt_pow32_of_uHi_lt_pow63
        (divKTrialCallV4Un21 uHi uLo vTop)
        (divKTrialCallV4DHi vTop)
        hdHi_ne hUn21_lt_pow63 hdHi_ge hdHi_lt

/-- V4 second-correction outer-guard no-fire preservation.

    If the high half of `Rhat2d` is nonzero, the second correction in
    `Q0dd` does not run and `Q0dd = Q0d`. Any lower bound already proved
    for `Q0d` therefore transfers unchanged to `Q0dd`. -/
theorem divKTrialCallV4Q0dd_ge_q_true_0_of_q0d_ge_of_rhat2d_hi_ne
    (uHi uLo vTop : Word)
    (hQ0d_ge :
      ((divKTrialCallV4Un21 uHi uLo vTop).toNat * 2^32 +
          (divKTrialCallV4Un0 uLo).toNat) /
        ((divKTrialCallV4DHi vTop).toNat * 2^32 +
          (divKTrialCallV4DLo vTop).toNat) ≤
      (divKTrialCallV4Q0d uHi uLo vTop).toNat)
    (hRhat2d_hi_ne :
      divKTrialCallV4Rhat2d uHi uLo vTop >>> (32 : BitVec 6).toNat ≠ 0) :
    ((divKTrialCallV4Un21 uHi uLo vTop).toNat * 2^32 +
        (divKTrialCallV4Un0 uLo).toNat) /
      ((divKTrialCallV4DHi vTop).toNat * 2^32 +
        (divKTrialCallV4DLo vTop).toNat) ≤
    (divKTrialCallV4Q0dd uHi uLo vTop).toNat := by
  rw [divKTrialCallV4Q0dd_unfold]
  unfold div128Quot_phase2b_q0'
  rw [if_neg hRhat2d_hi_ne]
  exact hQ0d_ge

/-- V4 second-correction inner-guard no-fire preservation.

    If `Rhat2d` has zero high half but the product check does not fire, the
    second correction again leaves `Q0dd = Q0d`. This is the companion
    no-fire case to
    `divKTrialCallV4Q0dd_ge_q_true_0_of_q0d_ge_of_rhat2d_hi_ne`. -/
theorem divKTrialCallV4Q0dd_ge_q_true_0_of_q0d_ge_of_rhat2d_hi_eq_zero_of_no_ult
    (uHi uLo vTop : Word)
    (hQ0d_ge :
      ((divKTrialCallV4Un21 uHi uLo vTop).toNat * 2^32 +
          (divKTrialCallV4Un0 uLo).toNat) /
        ((divKTrialCallV4DHi vTop).toNat * 2^32 +
          (divKTrialCallV4DLo vTop).toNat) ≤
      (divKTrialCallV4Q0d uHi uLo vTop).toNat)
    (hRhat2d_hi_zero :
      divKTrialCallV4Rhat2d uHi uLo vTop >>> (32 : BitVec 6).toNat = 0)
    (hNoUlt :
      ¬ BitVec.ult
        ((divKTrialCallV4Rhat2d uHi uLo vTop <<< (32 : BitVec 6).toNat) |||
          divKTrialCallV4Un0 uLo)
        (divKTrialCallV4Q0d uHi uLo vTop * divKTrialCallV4DLo vTop)) :
    ((divKTrialCallV4Un21 uHi uLo vTop).toNat * 2^32 +
        (divKTrialCallV4Un0 uLo).toNat) /
      ((divKTrialCallV4DHi vTop).toNat * 2^32 +
        (divKTrialCallV4DLo vTop).toNat) ≤
    (divKTrialCallV4Q0dd uHi uLo vTop).toNat := by
  rw [divKTrialCallV4Q0dd_unfold]
  unfold div128Quot_phase2b_q0'
  rw [if_pos hRhat2d_hi_zero]
  rw [if_neg hNoUlt]
  exact hQ0d_ge

/-- V4 second-correction fire preservation from a strict-overestimate witness.

    In the correction-fire branch, `Q0dd = Q0d - 1`. If a separate product
    check argument has already established that `Q0d` is strictly above the
    true second digit, then the decrement still leaves `Q0dd` at least the
    true digit. This isolates the small Word-decrement arithmetic from the
    remaining product-check bridge. -/
theorem divKTrialCallV4Q0dd_ge_q_true_0_of_q0d_gt_of_fire
    (uHi uLo vTop : Word)
    (hQ0d_gt :
      ((divKTrialCallV4Un21 uHi uLo vTop).toNat * 2^32 +
          (divKTrialCallV4Un0 uLo).toNat) /
        ((divKTrialCallV4DHi vTop).toNat * 2^32 +
          (divKTrialCallV4DLo vTop).toNat) <
      (divKTrialCallV4Q0d uHi uLo vTop).toNat)
    (hRhat2d_hi_zero :
      divKTrialCallV4Rhat2d uHi uLo vTop >>> (32 : BitVec 6).toNat = 0)
    (hUlt :
      BitVec.ult
        ((divKTrialCallV4Rhat2d uHi uLo vTop <<< (32 : BitVec 6).toNat) |||
          divKTrialCallV4Un0 uLo)
        (divKTrialCallV4Q0d uHi uLo vTop * divKTrialCallV4DLo vTop)) :
    ((divKTrialCallV4Un21 uHi uLo vTop).toNat * 2^32 +
        (divKTrialCallV4Un0 uLo).toNat) /
      ((divKTrialCallV4DHi vTop).toNat * 2^32 +
        (divKTrialCallV4DLo vTop).toNat) ≤
    (divKTrialCallV4Q0dd uHi uLo vTop).toNat := by
  rw [divKTrialCallV4Q0dd_unfold]
  unfold div128Quot_phase2b_q0'
  rw [if_pos hRhat2d_hi_zero]
  rw [if_pos hUlt]
  have hQ0d_pos : 0 < (divKTrialCallV4Q0d uHi uLo vTop).toNat :=
    Nat.lt_of_le_of_lt (Nat.zero_le _) hQ0d_gt
  have h_se_toNat : (signExtend12 4095 : Word).toNat = 2^64 - 1 := by decide
  have h_dec :
      (divKTrialCallV4Q0d uHi uLo vTop + signExtend12 4095).toNat =
        (divKTrialCallV4Q0d uHi uLo vTop).toNat - 1 := by
    rw [BitVec.toNat_add, h_se_toNat]
    have hQ0d_lt : (divKTrialCallV4Q0d uHi uLo vTop).toNat < 2^64 :=
      (divKTrialCallV4Q0d uHi uLo vTop).isLt
    omega
  rw [h_dec]
  omega

/-- Nat-level product-check bridge for the v4 Phase-2 second digit.

    This specializes the generic product-check implication to the v4 names:
    once `Q0d` and `Rhat2d` satisfy the Euclidean relation against `un21`,
    a strict product-check failure means `Q0d` is strictly above the true
    second Knuth digit. The remaining Word-level fire case only has to
    convert `BLTU ((Rhat2d << 32) | un0) (Q0d*dLo)` into `hProd_gt`. -/
theorem divKTrialCallV4Q0d_gt_q_true_0_of_prod_gt
    (uHi uLo vTop : Word)
    (hDen_pos :
      0 < (divKTrialCallV4DHi vTop).toNat * 2^32 +
        (divKTrialCallV4DLo vTop).toNat)
    (hRhat_eq :
      (divKTrialCallV4Rhat2d uHi uLo vTop).toNat =
        (divKTrialCallV4Un21 uHi uLo vTop).toNat -
          (divKTrialCallV4Q0d uHi uLo vTop).toNat *
            (divKTrialCallV4DHi vTop).toNat)
    (hQ0d_mul :
      (divKTrialCallV4Q0d uHi uLo vTop).toNat *
          (divKTrialCallV4DHi vTop).toNat ≤
        (divKTrialCallV4Un21 uHi uLo vTop).toNat)
    (hProd_gt :
      (divKTrialCallV4Q0d uHi uLo vTop).toNat *
          (divKTrialCallV4DLo vTop).toNat >
        (divKTrialCallV4Rhat2d uHi uLo vTop).toNat * 2^32 +
          (divKTrialCallV4Un0 uLo).toNat) :
    ((divKTrialCallV4Un21 uHi uLo vTop).toNat * 2^32 +
        (divKTrialCallV4Un0 uLo).toNat) /
      ((divKTrialCallV4DHi vTop).toNat * 2^32 +
        (divKTrialCallV4DLo vTop).toNat) <
    (divKTrialCallV4Q0d uHi uLo vTop).toNat := by
  exact EvmWord.product_check_gt_imp_overestimate
    (divKTrialCallV4Un21 uHi uLo vTop).toNat
    (divKTrialCallV4Un0 uLo).toNat
    (divKTrialCallV4DHi vTop).toNat
    (divKTrialCallV4DLo vTop).toNat
    (divKTrialCallV4Q0d uHi uLo vTop).toNat
    (divKTrialCallV4Rhat2d uHi uLo vTop).toNat
    (2^32)
    hDen_pos hRhat_eq hQ0d_mul hProd_gt

/-- Word-to-Nat bridge for the v4 Phase-2 product-check fire guard.

    When `Rhat2d` is a 32-bit value, the half-word combine
    `(Rhat2d << 32) | un0` has Nat value `Rhat2d * 2^32 + un0`.
    If the product `Q0d*dLo` is known not to wrap, the Word `BLTU` fire
    guard is exactly the Nat strict product inequality needed by
    `divKTrialCallV4Q0d_gt_q_true_0_of_prod_gt`. -/
theorem divKTrialCallV4Q0d_prod_gt_of_ult
    (uHi uLo vTop : Word)
    (hRhat2d_hi_zero :
      divKTrialCallV4Rhat2d uHi uLo vTop >>> (32 : BitVec 6).toNat = 0)
    (hUn0_lt : (divKTrialCallV4Un0 uLo).toNat < 2^32)
    (hProd_no_wrap :
      (divKTrialCallV4Q0d uHi uLo vTop *
          divKTrialCallV4DLo vTop).toNat =
        (divKTrialCallV4Q0d uHi uLo vTop).toNat *
          (divKTrialCallV4DLo vTop).toNat)
    (hUlt :
      BitVec.ult
        ((divKTrialCallV4Rhat2d uHi uLo vTop <<< (32 : BitVec 6).toNat) |||
          divKTrialCallV4Un0 uLo)
        (divKTrialCallV4Q0d uHi uLo vTop * divKTrialCallV4DLo vTop)) :
    (divKTrialCallV4Q0d uHi uLo vTop).toNat *
        (divKTrialCallV4DLo vTop).toNat >
      (divKTrialCallV4Rhat2d uHi uLo vTop).toNat * 2^32 +
        (divKTrialCallV4Un0 uLo).toNat := by
  have hRhat2d_lt : (divKTrialCallV4Rhat2d uHi uLo vTop).toNat < 2^32 := by
    have h_div : (divKTrialCallV4Rhat2d uHi uLo vTop).toNat / 2^32 = 0 := by
      have h_toNat :
          (divKTrialCallV4Rhat2d uHi uLo vTop >>> (32 : BitVec 6).toNat).toNat = 0 := by
        rw [hRhat2d_hi_zero]
        rfl
      rwa [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow] at h_toNat
    exact (Nat.div_eq_zero_iff.mp h_div).resolve_left (by decide)
  have hUlt_nat :
      (((divKTrialCallV4Rhat2d uHi uLo vTop <<< (32 : BitVec 6).toNat) |||
          divKTrialCallV4Un0 uLo).toNat) <
        (divKTrialCallV4Q0d uHi uLo vTop *
          divKTrialCallV4DLo vTop).toNat := by
    rwa [EvmWord.ult_iff] at hUlt
  rw [hProd_no_wrap] at hUlt_nat
  rw [show ((32 : BitVec 6).toNat : Nat) = 32 from rfl] at hUlt_nat
  rw [EvmWord.halfword_combine
        (divKTrialCallV4Rhat2d uHi uLo vTop)
        (divKTrialCallV4Un0 uLo) hRhat2d_lt hUn0_lt] at hUlt_nat
  exact hUlt_nat

/-- The V4 Phase-2 product `Q0d * DLo` does not wrap when `un21 < vTop`.

    This packages the standard `Q0d < 2^32` and `DLo < 2^32` bounds into the
    no-wrap equality consumed by `divKTrialCallV4Q0d_prod_gt_of_ult`. -/
theorem divKTrialCallV4Q0d_mul_DLo_no_wrap
    (uHi uLo vTop : Word)
    (hdHi_ge : (divKTrialCallV4DHi vTop).toNat ≥ 2^31)
    (hdHi_lt : (divKTrialCallV4DHi vTop).toNat < 2^32)
    (hdLo_lt : (divKTrialCallV4DLo vTop).toNat < 2^32)
    (hUn21_lt_vTop :
      (divKTrialCallV4Un21 uHi uLo vTop).toNat <
        (divKTrialCallV4DHi vTop).toNat * 2^32 +
          (divKTrialCallV4DLo vTop).toNat) :
    (divKTrialCallV4Q0d uHi uLo vTop *
        divKTrialCallV4DLo vTop).toNat =
      (divKTrialCallV4Q0d uHi uLo vTop).toNat *
        (divKTrialCallV4DLo vTop).toNat := by
  have hQ0d_lt : (divKTrialCallV4Q0d uHi uLo vTop).toNat < 2^32 :=
    divKTrialCallV4Q0d_lt_pow32 uHi uLo vTop
      hdHi_ge hdHi_lt hdLo_lt hUn21_lt_vTop
  have h_mul_lt :
      (divKTrialCallV4Q0d uHi uLo vTop).toNat *
          (divKTrialCallV4DLo vTop).toNat < 2^64 := by
    nlinarith
  rw [BitVec.toNat_mul]
  exact Nat.mod_eq_of_lt h_mul_lt

/-- V4 Phase-2 first-correction Euclidean postcondition.

    After the first Phase-2 product check, `Q0d` and `Rhat2d` still divide
    `un21` by the high divisor digit `DHi`: `Q0d * DHi + Rhat2d = un21`.
    This is the V4-name wrapper around the generic `div128Quot_phase2b_post`. -/
theorem divKTrialCallV4Q0d_Rhat2d_post
    (uHi uLo vTop : Word)
    (hdHi_ge : (divKTrialCallV4DHi vTop).toNat ≥ 2^31)
    (hdHi_lt : (divKTrialCallV4DHi vTop).toNat < 2^32) :
    (divKTrialCallV4Q0d uHi uLo vTop).toNat *
        (divKTrialCallV4DHi vTop).toNat +
      (divKTrialCallV4Rhat2d uHi uLo vTop).toNat =
    (divKTrialCallV4Un21 uHi uLo vTop).toNat := by
  have hdHi_ne : divKTrialCallV4DHi vTop ≠ 0 := by
    intro h_eq
    rw [h_eq] at hdHi_ge
    simp at hdHi_ge
  have h_post :
      (divKTrialCallV4Q0c uHi uLo vTop).toNat *
          (divKTrialCallV4DHi vTop).toNat +
        (divKTrialCallV4Rhat2c uHi uLo vTop).toNat =
      (divKTrialCallV4Un21 uHi uLo vTop).toNat := by
    unfold divKTrialCallV4Q0c divKTrialCallV4Rhat2c
    exact div128Quot_first_round_post
      (divKTrialCallV4Un21 uHi uLo vTop)
      (divKTrialCallV4DHi vTop)
      hdHi_ne hdHi_lt
  have h_rhat2c_lt :
      (divKTrialCallV4Rhat2c uHi uLo vTop).toNat <
        2 * (divKTrialCallV4DHi vTop).toNat := by
    unfold divKTrialCallV4Rhat2c
    exact div128Quot_rhatc_lt_2dHi
      (divKTrialCallV4Un21 uHi uLo vTop)
      (divKTrialCallV4DHi vTop)
      hdHi_ne hdHi_lt
  unfold divKTrialCallV4Q0d divKTrialCallV4Rhat2d
  exact
    @div128Quot_phase2b_post
      (divKTrialCallV4Un0 uLo)
      (divKTrialCallV4Un21 uHi uLo vTop)
      (divKTrialCallV4DHi vTop)
      hdHi_lt
      (divKTrialCallV4Q0c uHi uLo vTop)
      (divKTrialCallV4Rhat2c uHi uLo vTop)
      (divKTrialCallV4DLo vTop)
      h_post
      h_rhat2c_lt

/-- Consequences of `divKTrialCallV4Q0d_Rhat2d_post` in the shape consumed
    by the product-check bridge. -/
theorem divKTrialCallV4Q0d_Rhat2d_bridge
    (uHi uLo vTop : Word)
    (hdHi_ge : (divKTrialCallV4DHi vTop).toNat ≥ 2^31)
    (hdHi_lt : (divKTrialCallV4DHi vTop).toNat < 2^32) :
    (divKTrialCallV4Rhat2d uHi uLo vTop).toNat =
        (divKTrialCallV4Un21 uHi uLo vTop).toNat -
          (divKTrialCallV4Q0d uHi uLo vTop).toNat *
            (divKTrialCallV4DHi vTop).toNat ∧
      (divKTrialCallV4Q0d uHi uLo vTop).toNat *
          (divKTrialCallV4DHi vTop).toNat ≤
        (divKTrialCallV4Un21 uHi uLo vTop).toNat := by
  have h_post := divKTrialCallV4Q0d_Rhat2d_post uHi uLo vTop hdHi_ge hdHi_lt
  constructor <;> omega

end EvmAsm.Evm64
