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

end EvmAsm.Evm64
