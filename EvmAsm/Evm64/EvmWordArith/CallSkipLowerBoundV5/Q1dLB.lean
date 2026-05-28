/-
  EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV5.Q1dLB

  V5.5.0.4: unconditional Knuth-A LB on V5's post-Phase-1b-1st-correction
  quotient: `Q1d ≥ q_true_1`.

  Composes V5.5.0.2 (Q1c ≥ q_true_1) + V5.5.0.3 (1st-fire ⇒ strict)
  via case-split on the Phase-1b 1st correction firing:
  - No-fire: Q1d = Q1c ≥ q_true_1.
  - Fire: Q1d = Q1c - 1; strict gives q_true_1 < Q1c, so q_true_1 ≤ Q1c - 1 = Q1d.

  Bead `evm-asm-wbc4i.5.7` (V5.5.0.4). Prerequisite for V5.5.1.
-/

import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV5.Q1cStrictLT

namespace EvmAsm.Evm64

open EvmAsm.Rv64

theorem algorithmQ1dV5_ge_q_true_1
    (uHi uLo vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63)
    (huHi_lt_vTop : uHi.toNat < vTop.toNat) :
    (uHi.toNat * 2^32 + (divKTrialCallV5Un1 uLo).toNat) / vTop.toNat ≤
      (algorithmQ1dV5 uHi uLo vTop).toNat := by
  -- Knuth-A LB on Q1c (V5.5.0.2).
  have h_q1c_ge : (uHi.toNat * 2^32 + (divKTrialCallV5Un1 uLo).toNat) /
      vTop.toNat ≤ (algorithmQ1cV5 uHi vTop).toNat :=
    algorithmQ1cV5_ge_q_true_1 uHi uLo vTop hvTop_ge huHi_lt_vTop
  -- Case-split on Phase-1b 1st correction.
  by_cases h_fire : algorithmPhase1bFireV5 uHi uLo vTop
  · -- Fire: Q1d = Q1c + signExtend12 4095 (= Q1c - 1 mod 2^64).
    rw [algorithmQ1dV5_unfold]
    dsimp only
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
    -- Strict overshoot (V5.5.0.3): q_true_1 < Q1c.
    have h_strict :=
      algorithmQ1cV5_q_true_1_lt_of_phase1b_fire uHi uLo vTop hvTop_ge h_fire
    -- (Q1c + signExtend12 4095).toNat = Q1c.toNat - 1 (no-wrap since Q1c ≥ 1).
    have h_q1c_lt : (algorithmQ1cV5 uHi vTop).toNat < 2^32 :=
      algorithmQ1cV5_lt_pow32 uHi vTop
    have h_q1c_pos : (algorithmQ1cV5 uHi vTop).toNat ≥ 1 :=
      Nat.one_le_iff_ne_zero.mpr (fun h => by
        rw [h] at h_strict; exact Nat.not_lt_zero _ h_strict)
    have h_se : (signExtend12 4095 : Word).toNat = 2^64 - 1 := by decide
    rw [BitVec.toNat_add, h_se]
    have h_sum : (algorithmQ1cV5 uHi vTop).toNat + (2^64 - 1) =
        ((algorithmQ1cV5 uHi vTop).toNat - 1) + 2^64 := by omega
    have h_lt_pow64 : (algorithmQ1cV5 uHi vTop).toNat - 1 < 2^64 := by
      have : (algorithmQ1cV5 uHi vTop).toNat < 2^32 := h_q1c_lt
      have : (2 : Nat)^32 < 2^64 := by decide
      omega
    rw [h_sum, Nat.add_mod_right, Nat.mod_eq_of_lt h_lt_pow64]
    exact Nat.le_sub_one_of_lt h_strict
  · -- No-fire: Q1d = Q1c, LB is direct.
    rw [algorithmQ1dV5_eq_q1c_of_phase1b_no_fire uHi uLo vTop h_fire]
    exact h_q1c_ge

end EvmAsm.Evm64
