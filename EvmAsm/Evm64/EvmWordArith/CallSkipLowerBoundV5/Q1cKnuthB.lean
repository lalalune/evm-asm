/-
  EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV5.Q1cKnuthB

  Knuth-B upper bound on the V5 Phase-1a-corrected quotient:
  `Q1c.toNat ≤ q_true_1 + 2` under `vTop ≥ 2^63` and `uHi < vTop`,
  where `q_true_1 = (uHi*2^32 + un1) / vTop`.

  Mirror of v2's `algorithmQ1Prime_step3_q1c_le_q_true_1_plus_two`
  (`CallSkipLowerBoundV2/QuotientBounds.lean:284`), adapted to the V5
  cap. Sub-cases on the Phase-1a `hi1`:
  - `hi1 = 0`: Q1c = q1, direct from `trial_quotient_le` (Knuth-B).
  - `hi1 ≠ 0`: Q1c = 2^32 - 1; combined with `q1 ≥ 2^32` and Knuth-B
    `q1 ≤ q_true_1 + 2`, we get `q_true_1 ≥ 2^32 - 2 ≥ 2^32 - 3` so
    `Q1c = 2^32 - 1 ≤ q_true_1 + 2`.

  Bead `evm-asm-wbc4i.4.6.14` (V5.4.0.15). Prerequisite for V5.4.0.11
  (fire-case Q1d overshoot bound) and onward to V5.4.1.
-/

import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV5.Q1dEuclidean
import EvmAsm.Evm64.EvmWordArith.Div128Lemmas

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Knuth-B upper bound for V5's Phase-1a-corrected quotient. -/
theorem algorithmQ1cV5_le_q_true_1_plus_two
    (uHi uLo vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63)
    (huHi_lt_vTop : uHi.toNat < vTop.toNat) :
    (algorithmQ1cV5 uHi vTop).toNat ≤
      (uHi.toNat * 2^32 + (divKTrialCallV5Un1 uLo).toNat) / vTop.toNat + 2 := by
  set dHi := divKTrialCallV5DHi vTop with hdHi
  set dLo := divKTrialCallV5DLo vTop with hdLo
  set un1 := divKTrialCallV5Un1 uLo with hun1
  have h_dHi_ge : dHi.toNat ≥ 2^31 := by
    rw [hdHi]; unfold divKTrialCallV5DHi
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    omega
  have h_dHi_lt : dHi.toNat < 2^32 := by
    rw [hdHi]; exact divKTrialCallV5DHi_lt_pow32 vTop
  have h_dLo_lt : dLo.toNat < 2^32 := by
    rw [hdLo]; exact divKTrialCallV5DLo_lt_pow32 vTop
  have h_un1_lt : un1.toNat < 2^32 := by
    rw [hun1]; exact divKTrialCallV5Un1_lt_pow32 uLo
  have h_vTop_decomp : vTop.toNat = dHi.toNat * 2^32 + dLo.toNat := by
    rw [hdHi, hdLo]; unfold divKTrialCallV5DHi divKTrialCallV5DLo
    exact div128Quot_vTop_decomp vTop
  have h_uHi_lt : uHi.toNat < dHi.toNat * 2^32 + dLo.toNat := by
    rw [← h_vTop_decomp]; exact huHi_lt_vTop
  have h_dHi_ne : dHi ≠ 0 := by
    intro h
    have : dHi.toNat = 0 := by rw [h]; rfl
    omega
  -- q1.toNat = uHi.toNat / dHi.toNat
  set q1 : Word := rv64_divu uHi dHi with hq1
  have h_q1_eq : q1.toNat = uHi.toNat / dHi.toNat := by
    rw [hq1]; unfold rv64_divu
    have : ¬ (dHi == 0#64) := by simpa using h_dHi_ne
    rw [if_neg this, BitVec.toNat_udiv]
  -- Knuth-B: q1 ≤ q_true_1 + 2
  have h_q1_le : q1.toNat ≤
      (uHi.toNat * 2^32 + un1.toNat) / vTop.toNat + 2 := by
    rw [h_q1_eq, h_vTop_decomp]
    exact EvmWord.trial_quotient_le uHi.toNat un1.toNat dHi.toNat dLo.toNat
      h_dHi_lt h_dLo_lt h_un1_lt h_uHi_lt h_dHi_ge
  -- Case split on hi1
  rw [algorithmQ1cV5_unfold]
  dsimp only
  by_cases h_hi1 : q1 >>> (32 : BitVec 6).toNat = (0 : Word)
  · -- hi1 = 0: Q1c = q1
    simp only [hq1, hdHi] at h_hi1
    rw [if_pos h_hi1]
    -- Goal: q1.toNat ≤ ...
    have h_q1_eq' : (rv64_divu uHi (divKTrialCallV5DHi vTop)).toNat = q1.toNat := by
      rw [hq1]
    rw [h_q1_eq']
    exact h_q1_le
  · -- hi1 ≠ 0: Q1c = q1cCap = 2^32 - 1
    simp only [hq1, hdHi] at h_hi1
    rw [if_neg h_hi1]
    -- Goal: q1cCap.toNat ≤ ...
    have h_cap : ((BitVec.allOnes 64) >>> (32 : BitVec 6).toNat : Word).toNat = 2^32 - 1 := by
      decide
    rw [h_cap]
    -- q1 ≥ 2^32 (from hi1 ≠ 0)
    have h_q1_ge : q1.toNat ≥ 2^32 := by
      have h_shift : (q1 >>> (32 : BitVec 6).toNat).toNat = q1.toNat / 2^32 := by
        rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
      -- h_hi1 : q1 >>> 32 ≠ 0 (as Words), so its toNat is nonzero, so q1 / 2^32 ≥ 1.
      have h_ne_nat : (q1 >>> (32 : BitVec 6).toNat).toNat ≠ 0 := by
        intro h
        apply h_hi1
        exact BitVec.eq_of_toNat_eq (by simpa using h)
      omega
    omega

end EvmAsm.Evm64
