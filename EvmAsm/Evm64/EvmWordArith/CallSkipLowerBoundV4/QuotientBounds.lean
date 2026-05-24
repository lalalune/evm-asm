/-
  EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV4.QuotientBounds

  Word-to-Nat bridge wrappers for the v4 trial-call quotient digits.
  These keep downstream exact-quotient proofs phrased in terms of the
  source-of-truth `divKTrialCallV4*` definitions while reusing the generic
  Knuth lower-bound lemmas.
-/

import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV4.Algorithm
import EvmAsm.Evm64.EvmWordArith.Div128KnuthLower

namespace EvmAsm.Evm64

open EvmAsm.Rv64

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

end EvmAsm.Evm64
