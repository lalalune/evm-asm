/-
  EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV4.ExactQuotient

  Floor-shaped exact quotient surfaces for the v4 128/64 trial quotient.
  The heavier lower-bound arithmetic lives in `QuotientBounds`; this split
  module keeps those declarations available under names that match the final
  exact-quotient target without growing the near-cap source file.
-/

import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV4.QuotientBounds

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Exact v4 128/64 floor quotient when `un21` is the first-step
    mathematical remainder and the matching upper bound has been supplied. -/
theorem div128Quot_v4_eq_floor_of_un21_eq_r1_of_le
    (uHi uLo vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63)
    (huHi_lt_vTop : uHi.toNat < vTop.toNat)
    (huHi_lt_pow63 : uHi.toNat < 2^63)
    (hUn21_lt_vTop :
      (divKTrialCallV4Un21 uHi uLo vTop).toNat < vTop.toNat)
    (hUn21_eq_r1 :
      (divKTrialCallV4Un21 uHi uLo vTop).toNat =
        (uHi.toNat * 2^32 + (divKTrialCallV4Un1 uLo).toNat) % vTop.toNat)
    (h_le :
      (div128Quot_v4 uHi uLo vTop).toNat ≤
        (uHi.toNat * 2^64 + uLo.toNat) / vTop.toNat) :
    (div128Quot_v4 uHi uLo vTop).toNat =
      (uHi.toNat * 2^64 + uLo.toNat) / vTop.toNat :=
  div128Quot_v4_eq_q_true_of_un21_eq_r1_of_le uHi uLo vTop
    hvTop_ge huHi_lt_vTop huHi_lt_pow63 hUn21_lt_vTop hUn21_eq_r1 h_le

/-- Exact v4 128/64 floor quotient from the Phase-1 low-half no-wrap
    condition and the matching upper bound. -/
theorem div128Quot_v4_eq_floor_of_no_wrap_of_le
    (uHi uLo vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63)
    (huHi_lt_vTop : uHi.toNat < vTop.toNat)
    (huHi_lt_pow63 : uHi.toNat < 2^63)
    (hUn21_lt_vTop :
      (divKTrialCallV4Un21 uHi uLo vTop).toNat < vTop.toNat)
    (h_no_wrap :
      (divKTrialCallV4Q1dd uHi uLo vTop).toNat *
          (divKTrialCallV4DLo vTop).toNat ≤
        ((divKTrialCallV4Rhatdd uHi uLo vTop).toNat % 2^32) * 2^32 +
          (divKTrialCallV4Un1 uLo).toNat)
    (h_le :
      (div128Quot_v4 uHi uLo vTop).toNat ≤
        (uHi.toNat * 2^64 + uLo.toNat) / vTop.toNat) :
    (div128Quot_v4 uHi uLo vTop).toNat =
      (uHi.toNat * 2^64 + uLo.toNat) / vTop.toNat :=
  div128Quot_v4_eq_q_true_of_no_wrap_of_le uHi uLo vTop
    hvTop_ge huHi_lt_vTop huHi_lt_pow63 hUn21_lt_vTop h_no_wrap h_le

/-- Exact v4 128/64 floor quotient in the final Phase-1b high-half-zero
    branch, assuming the matching upper bound has been supplied. -/
theorem div128Quot_v4_eq_floor_of_rhatdd_hi_zero_of_le
    (uHi uLo vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63)
    (huHi_lt_vTop : uHi.toNat < vTop.toNat)
    (huHi_lt_pow63 : uHi.toNat < 2^63)
    (hUn21_lt_vTop :
      (divKTrialCallV4Un21 uHi uLo vTop).toNat < vTop.toNat)
    (h_rhat_hi_zero :
      divKTrialCallV4Rhatdd uHi uLo vTop >>> (32 : BitVec 6).toNat = (0 : Word))
    (h_le :
      (div128Quot_v4 uHi uLo vTop).toNat ≤
        (uHi.toNat * 2^64 + uLo.toNat) / vTop.toNat) :
    (div128Quot_v4 uHi uLo vTop).toNat =
      (uHi.toNat * 2^64 + uLo.toNat) / vTop.toNat :=
  div128Quot_v4_eq_q_true_of_rhatdd_hi_zero_of_le uHi uLo vTop
    hvTop_ge huHi_lt_vTop huHi_lt_pow63 hUn21_lt_vTop h_rhat_hi_zero h_le

end EvmAsm.Evm64
