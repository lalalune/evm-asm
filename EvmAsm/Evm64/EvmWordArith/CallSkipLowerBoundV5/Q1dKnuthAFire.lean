/-
  EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV5.Q1dKnuthAFire

  Knuth-A upper bound for the V5 post-Phase-1b-1st-correction quotient
  in the FIRE case: `Q1d.toNat ≤ q_true_1 + 1` under V5's fire condition
  (the `decide guard && BLTU` form).

  Composes V5.4.0.15 (Q1c ≤ q_true_1 + 2) with the fire-induced Q1c ≥ 1
  (from `q1c_pos_of_phase1b_fire`) to derive Q1d = Q1c - 1 ≤ q_true_1 + 1
  at the Nat level.

  Mirror of v4's `algorithmQ1dV4_le_qtrue_plus_one_of_phase1b_fire`
  (`CallSkipLowerBoundV4/Phase1bBound.lean:526`).

  Bead `evm-asm-wbc4i.4.6.15` (V5.4.0.16). Prerequisite for V5.4.0.11
  (fire-case overshoot bound) and onward to V5.4.1 / V5.4.2.
-/

import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV5.Q1cKnuthB

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- When V5 Phase-1b 1st correction fires, the post-correction quotient
    Q1d is at most `q_true_1 + 1`. -/
theorem algorithmQ1dV5_le_qtrue_plus_one_of_phase1b_fire
    (uHi uLo vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63)
    (huHi_lt_vTop : uHi.toNat < vTop.toNat)
    (h_fire : algorithmPhase1bFireV5 uHi uLo vTop) :
    (algorithmQ1dV5 uHi uLo vTop).toNat ≤
      (uHi.toNat * 2^32 + (divKTrialCallV5Un1 uLo).toNat) / vTop.toNat + 1 := by
  -- Knuth-B bound on Q1c
  have h_q1c_le : (algorithmQ1cV5 uHi vTop).toNat ≤
      (uHi.toNat * 2^32 + (divKTrialCallV5Un1 uLo).toNat) / vTop.toNat + 2 :=
    algorithmQ1cV5_le_q_true_1_plus_two uHi uLo vTop hvTop_ge huHi_lt_vTop
  -- Q1c ≥ 1 from fire (BLTU on q1c * dLo ≠ 0)
  have h_q1c_pos : (algorithmQ1cV5 uHi vTop).toNat ≥ 1 := by
    rw [algorithmPhase1bFireV5_unfold] at h_fire
    obtain ⟨_, h_ult⟩ := h_fire
    by_contra hq_lt
    push Not at hq_lt
    have hq_nat : (algorithmQ1cV5 uHi vTop).toNat = 0 := by omega
    have hq0 : algorithmQ1cV5 uHi vTop = 0 := BitVec.eq_of_toNat_eq hq_nat
    rw [algorithmRhatUn1cV5_unfold] at h_ult
    rw [hq0] at h_ult
    simp [BitVec.ult] at h_ult
  -- Q1c < 2^32 from cap (V5.4.0.4)
  have h_q1c_lt : (algorithmQ1cV5 uHi vTop).toNat < 2^32 :=
    algorithmQ1cV5_lt_pow32 uHi vTop
  -- Unfold Q1d and apply the fire-case branch
  rw [algorithmQ1dV5_unfold]
  dsimp only
  -- Show the if-condition is `true`
  have h_fire_cond :
      (decide (algorithmRhatcV5 uHi vTop >>> (32 : BitVec 6).toNat = 0) &&
        BitVec.ult
          ((algorithmRhatcV5 uHi vTop <<< (32 : BitVec 6).toNat) |||
            divKTrialCallV5Un1 uLo)
          (algorithmQ1cV5 uHi vTop * divKTrialCallV5DLo vTop)) = true := by
    rw [algorithmPhase1bFireV5_unfold] at h_fire
    rw [algorithmRhatUn1cV5_unfold] at h_fire
    obtain ⟨h_hi, h_ult⟩ := h_fire
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨h_hi, h_ult⟩
  rw [if_pos h_fire_cond]
  -- Q1c + signExtend12 4095 = Q1c - 1 mod 2^64 (no-wrap since Q1c ≥ 1)
  have h_se : (signExtend12 4095 : Word).toNat = 2^64 - 1 := by decide
  rw [BitVec.toNat_add, h_se]
  have h_sum : (algorithmQ1cV5 uHi vTop).toNat + (2^64 - 1) =
      ((algorithmQ1cV5 uHi vTop).toNat - 1) + 2^64 := by omega
  rw [h_sum, Nat.add_mod_right]
  rw [Nat.mod_eq_of_lt (by omega : (algorithmQ1cV5 uHi vTop).toNat - 1 < 2^64)]
  omega

end EvmAsm.Evm64
