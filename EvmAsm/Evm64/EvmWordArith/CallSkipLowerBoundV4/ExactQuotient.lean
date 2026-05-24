/-
  EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV4.ExactQuotient

  Floor-shaped exact quotient surfaces for the v4 128/64 trial quotient.
  The heavier lower-bound arithmetic lives in `QuotientBounds`; this split
  module keeps those declarations available under names that match the final
  exact-quotient target without growing the near-cap source file.
-/

import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV4.QuotientBounds
import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV2

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmWord (val256)

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

/-- V4 call-skip val256 lower bound from an exact 128/64 floor equality.

    This is the qHat-agnostic §B normalization bridge from v1 composed with
    a supplied exactness fact for `div128Quot_v4`. -/
theorem div128Quot_v4_call_skip_ge_val256_div_of_floor
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hb3nz : b3 ≠ 0)
    (hshift_nz : (clzResult b3).1 ≠ 0) :
    let shift := (clzResult b3).1.toNat % 64
    let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64
    let b3' := (b3 <<< shift) ||| (b2 >>> antiShift)
    let u4 := a3 >>> antiShift
    let u3 := (a3 <<< shift) ||| (a2 >>> antiShift)
    (div128Quot_v4 u4 u3 b3').toNat =
        (u4.toNat * 2^64 + u3.toNat) / b3'.toNat →
    val256 a0 a1 a2 a3 / val256 b0 b1 b2 b3 ≤
      (div128Quot_v4 u4 u3 b3').toNat := by
  intro shift antiShift b3' u4 u3 h_floor
  have h_bridge := q_true_triple_bridge_to_val256_norm
    a0 a1 a2 a3 b0 b1 b2 b3 hshift_nz hb3nz
  simp only [] at h_bridge
  rw [h_floor]
  exact h_bridge

end EvmAsm.Evm64
