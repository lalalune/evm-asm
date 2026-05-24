/-
  EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV4.Phase1bBound

  Algorithm-level Phase-1b facts for the v4 2-correction proof.
-/

import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV4.Algorithm
import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV4.Phase2bFireBound
import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV4.Phase2bNoFireBound
import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV2.QuotientBounds
import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV2.Un21Bridge

namespace EvmAsm.Evm64

open EvmAsm.Rv64 EvmWord

/-- The pre-second-correction Phase-1b quotient `q1'` used by v4. -/
@[irreducible]
def algorithmQ1dV4 (uHi uLo vTop : Word) : Word :=
  algorithmQ1Prime uHi uLo vTop

/-- The pre-second-correction Phase-1b remainder `rhat'` used by v4. -/
@[irreducible]
def algorithmRhatdV4 (uHi uLo vTop : Word) : Word :=
  let dHi := divKTrialCallV4DHi vTop
  let dLo := divKTrialCallV4DLo vTop
  let un1 := divKTrialCallV4Un1 uLo
  let q1 := rv64_divu uHi dHi
  let rhat := uHi - q1 * dHi
  let hi1 := q1 >>> (32 : BitVec 6).toNat
  let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
  let rhatc := if hi1 = 0 then rhat else rhat + dHi
  let qDlo := q1c * dLo
  let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| un1
  if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc

theorem algorithmQ1dV4_unfold (uHi uLo vTop : Word) :
    algorithmQ1dV4 uHi uLo vTop = algorithmQ1Prime uHi uLo vTop := by
  delta algorithmQ1dV4
  rfl

theorem algorithmRhatdV4_unfold (uHi uLo vTop : Word) :
    algorithmRhatdV4 uHi uLo vTop =
      (let dHi := divKTrialCallV4DHi vTop
       let dLo := divKTrialCallV4DLo vTop
       let un1 := divKTrialCallV4Un1 uLo
       let q1 := rv64_divu uHi dHi
       let rhat := uHi - q1 * dHi
       let hi1 := q1 >>> (32 : BitVec 6).toNat
       let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
       let rhatc := if hi1 = 0 then rhat else rhat + dHi
       let qDlo := q1c * dLo
       let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| un1
       if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc) := by
  delta algorithmRhatdV4
  rfl

/-- Phase-1b Euclidean identity for the v4 pre-second-correction pair. -/
theorem algorithmQ1dV4_rhatd_post
    (uHi uLo vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63) :
    (algorithmQ1dV4 uHi uLo vTop).toNat * (divKTrialCallV4DHi vTop).toNat +
      (algorithmRhatdV4 uHi uLo vTop).toNat = uHi.toNat := by
  have h := algorithmUn21_L2a_wrapped uHi uLo vTop hvTop_ge
  rw [algorithmQ1dV4_unfold, algorithmRhatdV4_unfold]
  unfold divKTrialCallV4DHi divKTrialCallV4DLo divKTrialCallV4Un1
  simpa using h

/-- V4 spelling of the Phase-1b no-wrap fact for the pre-second-correction
    product `q1' * dLo`. -/
theorem algorithmQ1dV4_dLo_no_wrap
    (uHi uLo vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63)
    (huHi_lt_vTop : uHi.toNat < vTop.toNat) :
    ((algorithmQ1dV4 uHi uLo vTop) * divKTrialCallV4DLo vTop).toNat =
      (algorithmQ1dV4 uHi uLo vTop).toNat * (divKTrialCallV4DLo vTop).toNat := by
  have h := algorithmUn21_L1b_q1_prime_dLo_no_wrap uHi uLo vTop hvTop_ge huHi_lt_vTop
  rw [algorithmQ1dV4_unfold]
  unfold algorithmQ1Prime divKTrialCallV4DLo
  simpa using h

/-- The normalized low divisor half extracted by the V4 call wrapper is a
    32-bit value. -/
theorem divKTrialCallV4DLo_lt_pow32 (vTop : Word) :
    (divKTrialCallV4DLo vTop).toNat < 2^32 := by
  unfold divKTrialCallV4DLo
  exact Word_ushiftRight_32_lt_pow32

/-- The high half of the low dividend word extracted by the V4 call wrapper is
    a 32-bit value. -/
theorem divKTrialCallV4Un1_lt_pow32 (uLo : Word) :
    (divKTrialCallV4Un1 uLo).toNat < 2^32 := by
  unfold divKTrialCallV4Un1
  exact Word_ushiftRight_32_lt_pow32

/-- The normalized high divisor half extracted by the V4 call wrapper is a
    32-bit value. -/
theorem divKTrialCallV4DHi_lt_pow32 (vTop : Word) :
    (divKTrialCallV4DHi vTop).toNat < 2^32 := by
  unfold divKTrialCallV4DHi
  exact Word_ushiftRight_32_lt_pow32

/-- Under normalization, the high divisor half extracted by the V4 call wrapper
    is nonzero. -/
theorem divKTrialCallV4DHi_ne_of_ge
    (vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63) :
    divKTrialCallV4DHi vTop ≠ 0 := by
  intro hzero
  have hnat : (divKTrialCallV4DHi vTop).toNat = 0 := by rw [hzero]; rfl
  unfold divKTrialCallV4DHi at hnat
  rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow] at hnat
  omega

/-- In the complementary wide-`uHi` regime, Phase 1a's high-half correction
    definitely fires. -/
theorem divKTrialCallV4Q1_hi_ne_zero_of_dHi_pow32_le_uHi
    (uHi vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63)
    (huHi_ge_dHi_pow32 :
      (divKTrialCallV4DHi vTop).toNat * 2^32 ≤ uHi.toNat) :
    (rv64_divu uHi (divKTrialCallV4DHi vTop)) >>>
        (32 : BitVec 6).toNat ≠ (0 : Word) := by
  let dHi := divKTrialCallV4DHi vTop
  have hdHi_ne : dHi ≠ 0 := by
    simpa [dHi] using divKTrialCallV4DHi_ne_of_ge vTop hvTop_ge
  have hq_ge : (rv64_divu uHi dHi).toNat ≥ 2^32 := by
    rw [rv64_divu_toNat uHi dHi hdHi_ne]
    apply (Nat.le_div_iff_mul_le ?_).mpr
    · nlinarith [huHi_ge_dHi_pow32]
    · have : dHi.toNat ≠ 0 := by
        intro h0
        exact hdHi_ne (BitVec.eq_of_toNat_eq h0)
      omega
  intro hzero
  have hlt : (rv64_divu uHi dHi).toNat < 2^32 := by
    have h := (ushiftRight_eq_zero_iff (val := rv64_divu uHi dHi)
      ((32 : BitVec 6).toNat)).mp hzero
    simpa using h
  omega

/-- Nat form of subtracting one from a Phase-1a quotient whose high half is
    nonzero. -/
theorem phase1a_q1_dec_toNat_of_hi_ne_zero
    (q1 : Word)
    (hhi : q1 >>> (32 : BitVec 6).toNat ≠ (0 : Word)) :
    (q1 + signExtend12 4095).toNat = q1.toNat - 1 := by
  have hq_ge := (ushiftRight_ne_zero_iff (val := q1) ((32 : BitVec 6).toNat)).mp hhi
  have hq_pos : q1.toNat ≥ 1 := by
    rw [show ((32 : BitVec 6).toNat : Nat) = 32 from by rfl] at hq_ge
    omega
  have h_se_toNat : (signExtend12 4095 : Word).toNat = 2^64 - 1 := by decide
  rw [BitVec.toNat_add, h_se_toNat]
  omega

/-- In the wide-`uHi` regime, the Phase-1a corrected quotient is `q1 - 1`. -/
theorem divKTrialCallV4Q1c_toNat_of_dHi_pow32_le_uHi
    (uHi vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63)
    (huHi_ge_dHi_pow32 :
      (divKTrialCallV4DHi vTop).toNat * 2^32 ≤ uHi.toNat) :
    let dHi := divKTrialCallV4DHi vTop
    let q1 := rv64_divu uHi dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    q1c.toNat = q1.toNat - 1 := by
  intro dHi q1 hi1 q1c
  have hhi : q1 >>> (32 : BitVec 6).toNat ≠ (0 : Word) := by
    simpa [dHi, q1] using
      divKTrialCallV4Q1_hi_ne_zero_of_dHi_pow32_le_uHi
        uHi vTop hvTop_ge huHi_ge_dHi_pow32
  show (if hi1 = 0 then q1 else q1 + signExtend12 4095).toNat = q1.toNat - 1
  rw [if_neg hhi]
  exact phase1a_q1_dec_toNat_of_hi_ne_zero q1 hhi

/-- In the wide-`uHi` regime, the Phase-1a corrected remainder is
    `rhat + dHi`. -/
theorem divKTrialCallV4Rhatc_eq_of_dHi_pow32_le_uHi
    (uHi vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63)
    (huHi_ge_dHi_pow32 :
      (divKTrialCallV4DHi vTop).toNat * 2^32 ≤ uHi.toNat) :
    let dHi := divKTrialCallV4DHi vTop
    let q1 := rv64_divu uHi dHi
    let rhat := uHi - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    rhatc = rhat + dHi := by
  intro dHi q1 rhat hi1 rhatc
  have hhi : q1 >>> (32 : BitVec 6).toNat ≠ (0 : Word) := by
    simpa [dHi, q1] using
      divKTrialCallV4Q1_hi_ne_zero_of_dHi_pow32_le_uHi
        uHi vTop hvTop_ge huHi_ge_dHi_pow32
  show (if hi1 = 0 then rhat else rhat + dHi) = rhat + dHi
  rw [if_neg hhi]

/-- In the wide-`uHi` regime, the Phase-1a corrected quotient is at most
    `2^32`. -/
theorem divKTrialCallV4Q1c_le_pow32_of_dHi_pow32_le_uHi
    (uHi vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63)
    (huHi_lt_vTop : uHi.toNat < vTop.toNat)
    (huHi_ge_dHi_pow32 :
      (divKTrialCallV4DHi vTop).toNat * 2^32 ≤ uHi.toNat) :
    let dHi := divKTrialCallV4DHi vTop
    let q1 := rv64_divu uHi dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    q1c.toNat ≤ 2^32 := by
  intro dHi q1 hi1 q1c
  have h_q1c_eq0 := divKTrialCallV4Q1c_toNat_of_dHi_pow32_le_uHi
    uHi vTop hvTop_ge huHi_ge_dHi_pow32
  have h_q1c_eq : q1c.toNat = q1.toNat - 1 := by
    simpa [dHi, q1, hi1, q1c] using h_q1c_eq0
  have hdHi_ne : dHi ≠ 0 := by
    simpa [dHi] using divKTrialCallV4DHi_ne_of_ge vTop hvTop_ge
  have hdHi_pos : 0 < dHi.toNat := by
    have : dHi.toNat ≠ 0 := by
      intro h0
      exact hdHi_ne (BitVec.eq_of_toNat_eq h0)
    omega
  have hdHi_ge : dHi.toNat ≥ 2^31 := by
    unfold dHi divKTrialCallV4DHi
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    omega
  have hq1_eq : q1.toNat = uHi.toNat / dHi.toNat := by
    simpa [dHi, q1] using rv64_divu_toNat uHi dHi hdHi_ne
  have h_vTop_decomp : vTop.toNat = dHi.toNat * 2^32 +
      (divKTrialCallV4DLo vTop).toNat := by
    unfold dHi divKTrialCallV4DHi divKTrialCallV4DLo
    exact div128Quot_vTop_decomp vTop
  have h_dLo_lt : (divKTrialCallV4DLo vTop).toNat < 2^32 :=
    divKTrialCallV4DLo_lt_pow32 vTop
  have h_dLo_le_two_dHi_pred : (divKTrialCallV4DLo vTop).toNat ≤
      2 * dHi.toNat - 1 := by
    have hpow : (2^32 : Nat) = 2 * 2^31 := by decide
    omega
  have h_uHi_le0 : uHi.toNat ≤ dHi.toNat * 2^32 + (2 * dHi.toNat - 1) := by
    rw [h_vTop_decomp] at huHi_lt_vTop
    omega
  have h_rhs_le : dHi.toNat * 2^32 + (2 * dHi.toNat - 1) ≤
      dHi.toNat * (2^32 + 1) + (dHi.toNat - 1) := by
    have h_two : 2 * dHi.toNat - 1 = dHi.toNat + (dHi.toNat - 1) := by omega
    rw [h_two]
    ring_nf
    rfl
  have h_uHi_le : uHi.toNat ≤ dHi.toNat * (2^32 + 1) + (dHi.toNat - 1) :=
    le_trans h_uHi_le0 h_rhs_le
  have hq1_le : q1.toNat ≤ 2^32 + 1 := by
    rw [hq1_eq]
    exact (Nat.div_le_iff_le_mul_add_pred hdHi_pos).mpr h_uHi_le
  rw [h_q1c_eq]
  omega

/-- In the wide-`uHi` regime, the V4 pre-second-correction quotient is at most
    `2^32`. -/
theorem algorithmQ1dV4_le_pow32_of_dHi_pow32_le_uHi
    (uHi uLo vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63)
    (huHi_lt_vTop : uHi.toNat < vTop.toNat)
    (huHi_ge_dHi_pow32 :
      (divKTrialCallV4DHi vTop).toNat * 2^32 ≤ uHi.toNat) :
    (algorithmQ1dV4 uHi uLo vTop).toNat ≤ 2^32 := by
  let dHi := divKTrialCallV4DHi vTop
  let dLo := divKTrialCallV4DLo vTop
  let un1 := divKTrialCallV4Un1 uLo
  let q1 := rv64_divu uHi dHi
  let rhat := uHi - q1 * dHi
  let hi1 := q1 >>> (32 : BitVec 6).toNat
  let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
  let rhatc := if hi1 = 0 then rhat else rhat + dHi
  let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| un1
  have h_q1c_le : q1c.toNat ≤ 2^32 := by
    have h := divKTrialCallV4Q1c_le_pow32_of_dHi_pow32_le_uHi
      uHi vTop hvTop_ge huHi_lt_vTop huHi_ge_dHi_pow32
    simpa [dHi, q1, hi1, q1c] using h
  have h_prime_le : (algorithmQ1dV4 uHi uLo vTop).toNat ≤ q1c.toNat := by
    rw [algorithmQ1dV4_unfold]
    unfold algorithmQ1Prime
    have h := div128Quot_q1_prime_le_q1c q1c dLo rhatUn1
    simpa [dHi, dLo, un1, q1, rhat, hi1, q1c, rhatc, rhatUn1,
      divKTrialCallV4DHi, divKTrialCallV4DLo, divKTrialCallV4Un1] using h
  exact le_trans h_prime_le h_q1c_le

/-- V4 spelling of the generic Phase-1b upper bound `q1' ≤ 2^32 + 1`. -/
theorem algorithmQ1dV4_le_pow32_plus_one
    (uHi uLo vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63)
    (huHi_lt_vTop : uHi.toNat < vTop.toNat) :
    (algorithmQ1dV4 uHi uLo vTop).toNat ≤ 2^32 + 1 := by
  have hdHi_ge : (divKTrialCallV4DHi vTop).toNat ≥ 2^31 := by
    unfold divKTrialCallV4DHi
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have h2 : (2^63 : Nat) = 2^31 * 2^32 := by decide
    omega
  have hdLo_lt : (divKTrialCallV4DLo vTop).toNat < 2^32 :=
    divKTrialCallV4DLo_lt_pow32 vTop
  have h_vTop_decomp : vTop.toNat =
      (divKTrialCallV4DHi vTop).toNat * 2^32 +
        (divKTrialCallV4DLo vTop).toNat := by
    unfold divKTrialCallV4DHi divKTrialCallV4DLo
    exact div128Quot_vTop_decomp vTop
  have huHi_lt_vTop_decomp : uHi.toNat <
      (divKTrialCallV4DHi vTop).toNat * 2^32 +
        (divKTrialCallV4DLo vTop).toNat := by
    rw [← h_vTop_decomp]
    exact huHi_lt_vTop
  let dHi := divKTrialCallV4DHi vTop
  let dLo := divKTrialCallV4DLo vTop
  let un1 := divKTrialCallV4Un1 uLo
  let q1 := rv64_divu uHi dHi
  let rhat := uHi - q1 * dHi
  let hi1 := q1 >>> (32 : BitVec 6).toNat
  let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
  let rhatc := if hi1 = 0 then rhat else rhat + dHi
  let qDlo := q1c * dLo
  let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| un1
  have h := div128Quot_q1_prime_le_pow32_plus_one uHi dHi dLo rhatUn1
    hdHi_ge hdLo_lt huHi_lt_vTop_decomp
  rw [algorithmQ1dV4_unfold]
  unfold algorithmQ1Prime
  simpa [dHi, dLo, un1, q1, rhat, hi1, q1c, rhatc, qDlo, rhatUn1,
    divKTrialCallV4DHi, divKTrialCallV4DLo, divKTrialCallV4Un1] using h

/-- If the high half of `rhat` is zero and `dHi` is a 32-bit halfword, then
    adding `dHi` to `rhat` cannot wrap a 64-bit word. -/
theorem phase2b_rhat_add_dHi_no_wrap_of_hi_zero
    (rhat dHi : Word)
    (h_rhat_hi_zero : rhat >>> (32 : BitVec 6).toNat = (0 : Word))
    (h_dHi_lt : dHi.toNat < 2^32) :
    (rhat + dHi).toNat = rhat.toNat + dHi.toNat := by
  have h_rhat_lt : rhat.toNat < 2^32 := by
    have h := (ushiftRight_eq_zero_iff (val := rhat) ((32 : BitVec 6).toNat)).mp
      h_rhat_hi_zero
    simpa using h
  have h_sum_lt : rhat.toNat + dHi.toNat < 2^64 := by omega
  rw [BitVec.toNat_add]
  omega

/-- A true second-correction unsigned comparison against `q * dLo` implies
    the trial quotient `q` is nonzero. -/
theorem phase2b_q_pos_of_fire_ult
    (q dLo lhs : Word)
    (h_ult : BitVec.ult lhs (q * dLo)) :
    q.toNat ≥ 1 := by
  by_contra hq_lt
  push Not at hq_lt
  have hq_nat : q.toNat = 0 := by omega
  have hq0 : q = 0 := BitVec.eq_of_toNat_eq hq_nat
  subst q
  have h_false : ¬ BitVec.ult lhs ((0 : Word) * dLo) := by
    simp [BitVec.ult]
  exact h_false h_ult

/-- The V4 final Phase-1b quotient wrapper is the generic second-correction
    quotient instantiated with the v4 pre-second-correction pair. -/
theorem divKTrialCallV4Q1dd_eq_phase2b_algorithm
    (uHi uLo vTop : Word) :
    divKTrialCallV4Q1dd uHi uLo vTop =
      div128Quot_phase2b_q0'
        (algorithmQ1dV4 uHi uLo vTop)
        (algorithmRhatdV4 uHi uLo vTop)
        (divKTrialCallV4DLo vTop)
        (divKTrialCallV4Un1 uLo) := by
  rw [← div128Quot_phase2b_q0'_and_form]
  rw [algorithmQ1dV4_unfold, algorithmRhatdV4_unfold]
  unfold algorithmQ1Prime divKTrialCallV4Q1dd
  unfold divKTrialCallV4DHi divKTrialCallV4DLo divKTrialCallV4Un1
  rfl

/-- The V4 final Phase-1b remainder wrapper is the generic second-correction
    remainder update instantiated with the v4 pre-second-correction pair. -/
theorem divKTrialCallV4Rhatdd_eq_phase2b_algorithm
    (uHi uLo vTop : Word) :
    divKTrialCallV4Rhatdd uHi uLo vTop =
      (if (algorithmRhatdV4 uHi uLo vTop) >>> (32 : BitVec 6).toNat = (0 : Word) ∧
          BitVec.ult
            (((algorithmRhatdV4 uHi uLo vTop) <<< (32 : BitVec 6).toNat) |||
              divKTrialCallV4Un1 uLo)
            ((algorithmQ1dV4 uHi uLo vTop) * divKTrialCallV4DLo vTop) then
        algorithmRhatdV4 uHi uLo vTop + divKTrialCallV4DHi vTop
       else
        algorithmRhatdV4 uHi uLo vTop) := by
  rw [algorithmQ1dV4_unfold, algorithmRhatdV4_unfold]
  unfold algorithmQ1Prime divKTrialCallV4Rhatdd
  unfold divKTrialCallV4DHi divKTrialCallV4DLo divKTrialCallV4Un1
  rfl

/-- Narrow-call Phase-1b overshoot bound for the pre-second-correction pair.

    This discharges the `h_overshoot_le_vTop` argument of
    `div128Quot_phase2b_q0'_dLo_bound_fire_case` in the
    `uHi < dHi * 2^32` sub-regime. -/
theorem algorithmQ1dV4_dLo_overshoot_le_vTop_of_uHi_lt_dHi_pow32
    (uHi uLo vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63)
    (huHi_lt_vTop : uHi.toNat < vTop.toNat)
    (huHi_lt_dHi_pow32 :
      uHi.toNat < (divKTrialCallV4DHi vTop).toNat * 2^32)
    (h_phase1b_post :
      (algorithmQ1dV4 uHi uLo vTop).toNat * (divKTrialCallV4DHi vTop).toNat +
        (algorithmRhatdV4 uHi uLo vTop).toNat = uHi.toNat) :
    (algorithmQ1dV4 uHi uLo vTop).toNat * (divKTrialCallV4DLo vTop).toNat ≤
      (algorithmRhatdV4 uHi uLo vTop).toNat * 2^32 +
        (divKTrialCallV4Un1 uLo).toNat +
        (divKTrialCallV4DHi vTop).toNat * 2^32 +
        (divKTrialCallV4DLo vTop).toNat := by
  have h_vTop_decomp : vTop.toNat =
      (divKTrialCallV4DHi vTop).toNat * 2^32 +
        (divKTrialCallV4DLo vTop).toNat := by
    unfold divKTrialCallV4DHi divKTrialCallV4DLo
    exact div128Quot_vTop_decomp vTop
  have h_q_le0 := algorithmQ1Prime_le_q_true_1_plus_one uHi uLo vTop
    hvTop_ge huHi_lt_vTop (by simpa [divKTrialCallV4DHi] using huHi_lt_dHi_pow32)
  have h_q_le :
      (algorithmQ1dV4 uHi uLo vTop).toNat ≤
        (uHi.toNat * 2^32 + (divKTrialCallV4Un1 uLo).toNat) / vTop.toNat + 1 := by
    rw [algorithmQ1dV4_unfold]
    unfold divKTrialCallV4Un1
    simpa using h_q_le0
  have h_vTop_pos : 0 < vTop.toNat := by omega
  have h_qV_le :
      (algorithmQ1dV4 uHi uLo vTop).toNat * vTop.toNat ≤
        (uHi.toNat * 2^32 + (divKTrialCallV4Un1 uLo).toNat) + vTop.toNat := by
    have h_mul := Nat.mul_le_mul_right vTop.toNat h_q_le
    have h_div_mul :=
      Nat.div_mul_le_self
        (uHi.toNat * 2^32 + (divKTrialCallV4Un1 uLo).toNat) vTop.toNat
    nlinarith
  have h_u_decomp : uHi.toNat * 2^32 =
      (algorithmQ1dV4 uHi uLo vTop).toNat * (divKTrialCallV4DHi vTop).toNat * 2^32 +
        (algorithmRhatdV4 uHi uLo vTop).toNat * 2^32 := by
    have h := congrArg (fun x => x * 2^32) h_phase1b_post
    nlinarith [Nat.add_mul
      ((algorithmQ1dV4 uHi uLo vTop).toNat * (divKTrialCallV4DHi vTop).toNat)
      (algorithmRhatdV4 uHi uLo vTop).toNat (2^32)]
  have h_qV_expand :
      (algorithmQ1dV4 uHi uLo vTop).toNat * vTop.toNat =
        (algorithmQ1dV4 uHi uLo vTop).toNat * (divKTrialCallV4DHi vTop).toNat * 2^32 +
          (algorithmQ1dV4 uHi uLo vTop).toNat * (divKTrialCallV4DLo vTop).toNat := by
    rw [h_vTop_decomp]
    ring
  nlinarith

/-- Narrow-call Phase-1b overshoot bound, with the Phase-1b Euclidean identity
    discharged internally. -/
theorem algorithmQ1dV4_dLo_overshoot_le_vTop_of_uHi_lt_dHi_pow32_closed
    (uHi uLo vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63)
    (huHi_lt_vTop : uHi.toNat < vTop.toNat)
    (huHi_lt_dHi_pow32 :
      uHi.toNat < (divKTrialCallV4DHi vTop).toNat * 2^32) :
    (algorithmQ1dV4 uHi uLo vTop).toNat * (divKTrialCallV4DLo vTop).toNat ≤
      (algorithmRhatdV4 uHi uLo vTop).toNat * 2^32 +
        (divKTrialCallV4Un1 uLo).toNat +
        (divKTrialCallV4DHi vTop).toNat * 2^32 +
        (divKTrialCallV4DLo vTop).toNat := by
  exact algorithmQ1dV4_dLo_overshoot_le_vTop_of_uHi_lt_dHi_pow32
    uHi uLo vTop hvTop_ge huHi_lt_vTop huHi_lt_dHi_pow32
    (algorithmQ1dV4_rhatd_post uHi uLo vTop hvTop_ge)

/-- Narrow-call V4 Phase-1b post-condition after the second correction.

    This composes the generic Phase-2b fire/no-fire bounds with the V4
    pre-second-correction pair and the narrow-regime overshoot discharge. -/
theorem divKTrialCallV4_phase1b_dLo_bound_of_uHi_lt_dHi_pow32
    (uHi uLo vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63)
    (huHi_lt_vTop : uHi.toNat < vTop.toNat)
    (huHi_lt_dHi_pow32 :
      uHi.toNat < (divKTrialCallV4DHi vTop).toNat * 2^32) :
    (divKTrialCallV4Q1dd uHi uLo vTop).toNat *
        (divKTrialCallV4DLo vTop).toNat ≤
      (divKTrialCallV4Rhatdd uHi uLo vTop).toNat * 2^32 +
        (divKTrialCallV4Un1 uLo).toNat := by
  let q := algorithmQ1dV4 uHi uLo vTop
  let rhat := algorithmRhatdV4 uHi uLo vTop
  let dHi := divKTrialCallV4DHi vTop
  let dLo := divKTrialCallV4DLo vTop
  let un := divKTrialCallV4Un1 uLo
  have h_q_le : q.toNat ≤ 2^32 + 1 := by
    simpa [q] using algorithmQ1dV4_le_pow32_plus_one uHi uLo vTop hvTop_ge huHi_lt_vTop
  have h_dLo_lt : dLo.toNat < 2^32 := by
    simpa [dLo] using divKTrialCallV4DLo_lt_pow32 vTop
  have h_un_lt : un.toNat < 2^32 := by
    simpa [un] using divKTrialCallV4Un1_lt_pow32 uLo
  have h_no_wrap_q : (q * dLo).toNat = q.toNat * dLo.toNat := by
    simpa [q, dLo] using algorithmQ1dV4_dLo_no_wrap uHi uLo vTop hvTop_ge huHi_lt_vTop
  have h_overshoot : q.toNat * dLo.toNat ≤
      rhat.toNat * 2^32 + un.toNat + dHi.toNat * 2^32 + dLo.toNat := by
    simpa [q, rhat, dHi, dLo, un] using
      algorithmQ1dV4_dLo_overshoot_le_vTop_of_uHi_lt_dHi_pow32_closed
        uHi uLo vTop hvTop_ge huHi_lt_vTop huHi_lt_dHi_pow32
  by_cases h_guard : rhat >>> (32 : BitVec 6).toNat = (0 : Word) ∧
    BitVec.ult ((rhat <<< (32 : BitVec 6).toNat) ||| un) (q * dLo)
  · have h_guard_full := h_guard
    obtain ⟨h_rhat_hi_zero, h_ult⟩ := h_guard
    have h_dHi_lt : dHi.toNat < 2^32 := by
      unfold dHi divKTrialCallV4DHi
      exact Word_ushiftRight_32_lt_pow32
    have h_no_wrap_rhat : (rhat + dHi).toNat = rhat.toNat + dHi.toNat :=
      phase2b_rhat_add_dHi_no_wrap_of_hi_zero rhat dHi h_rhat_hi_zero h_dHi_lt
    have h_q_pos : q.toNat ≥ 1 :=
      phase2b_q_pos_of_fire_ult q dLo ((rhat <<< (32 : BitVec 6).toNat) ||| un) h_ult
    obtain ⟨h_qeq, h_bound⟩ := div128Quot_phase2b_q0'_dLo_bound_fire_case
      q rhat dLo dHi un h_no_wrap_rhat h_q_pos h_rhat_hi_zero h_ult h_overshoot
    rw [divKTrialCallV4Q1dd_eq_phase2b_algorithm,
      divKTrialCallV4Rhatdd_eq_phase2b_algorithm]
    change (div128Quot_phase2b_q0' q rhat dLo un).toNat * dLo.toNat ≤
      (if rhat >>> (32 : BitVec 6).toNat = (0 : Word) ∧
        BitVec.ult ((rhat <<< (32 : BitVec 6).toNat) ||| un) (q * dLo) then
        rhat + dHi else rhat).toNat * 2^32 + un.toNat
    rw [h_qeq, if_pos h_guard_full]
    exact h_bound
  · obtain ⟨h_qeq, h_bound⟩ := div128Quot_phase2b_q0'_dLo_bound_no_fire
      q rhat dLo un h_q_le h_dLo_lt h_un_lt h_no_wrap_q h_guard
    rw [divKTrialCallV4Q1dd_eq_phase2b_algorithm,
      divKTrialCallV4Rhatdd_eq_phase2b_algorithm]
    change (div128Quot_phase2b_q0' q rhat dLo un).toNat * dLo.toNat ≤
      (if rhat >>> (32 : BitVec 6).toNat = (0 : Word) ∧
        BitVec.ult ((rhat <<< (32 : BitVec 6).toNat) ||| un) (q * dLo) then
        rhat + dHi else rhat).toNat * 2^32 + un.toNat
    rw [h_qeq, if_neg h_guard]
    exact h_bound

end EvmAsm.Evm64
