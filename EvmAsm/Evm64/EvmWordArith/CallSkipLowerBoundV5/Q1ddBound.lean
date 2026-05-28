/-
  EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV5.Q1ddBound

  V5.4.2: the V5 post-Phase-1b-2nd-correction quotient does not overshoot
  the abstract first 128/64 quotient digit:

    Q1dd.toNat ≤ q_true_1 = (uHi * 2^32 + un1) / vTop

  Builds on V5.4.1 (`divKTrialCallV5_phase1b_dLo_bound`) and the V5.4.0
  Euclidean foundations to derive the Nat-level inequality.

  Mirror of v4's `divKTrialCallV4Q1dd_le_q_true_1`
  (`CallSkipLowerBoundV4/Phase1bBound.lean:1105`).

  Bead `evm-asm-wbc4i.4.2` (V5.4.2).
-/

import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV5.Phase1bBound

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Phase-1b 2-correction Euclidean identity at the V5 irreducible level:
    `Q1dd * dHi + Rhatdd = uHi`. Lifts the algorithm-level
    `algorithmQ1dV5_rhatd_post` (V5.4.0.12, post-1st-correction) to the
    post-2nd-correction Q1dd/Rhatdd irreducibles. -/
theorem divKTrialCallV5Q1dd_rhatdd_post
    (uHi uLo vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63) :
    (divKTrialCallV5Q1dd uHi uLo vTop).toNat *
        (divKTrialCallV5DHi vTop).toNat +
      (divKTrialCallV5Rhatdd uHi uLo vTop).toNat =
      uHi.toNat := by
  have h_pre := algorithmQ1dV5_rhatd_post uHi uLo vTop hvTop_ge
  rw [divKTrialCallV5Q1dd_eq_alg, divKTrialCallV5Rhatdd_eq_alg]
  set q := algorithmQ1dV5 uHi uLo vTop with hq
  set rhat := algorithmRhatdV5 uHi uLo vTop with hrhat
  set dHi := divKTrialCallV5DHi vTop with hdHi
  set dLo := divKTrialCallV5DLo vTop with hdLo
  set un := divKTrialCallV5Un1 uLo with hun
  -- The Q1dd bridge gives `div128Quot_phase2b_q0' q rhat dLo un`.
  -- The Rhatdd bridge gives nested-if form.
  -- Case-split on the Phase-1b 2nd correction guard (rhat>>>32 = 0 AND BLTU).
  by_cases h_outer : rhat >>> (32 : BitVec 6).toNat = (0 : Word)
  · rw [if_pos h_outer]
    by_cases h_inner :
        BitVec.ult ((rhat <<< (32 : BitVec 6).toNat) ||| un) (q * dLo)
    · -- Fire: Q1dd = q + signExtend12 4095 (= q - 1 if q ≥ 1), Rhatdd = rhat + dHi.
      rw [if_pos h_inner]
      have h_dHi_lt : dHi.toNat < 2^32 := divKTrialCallV5DHi_lt_pow32 vTop
      have h_no_wrap_rhat : (rhat + dHi).toNat = rhat.toNat + dHi.toNat :=
        phase2b_rhat_add_dHi_no_wrap_of_hi_zero rhat dHi h_outer h_dHi_lt
      have h_q_pos : q.toNat ≥ 1 :=
        phase2b_q_pos_of_fire_ult q dLo
          ((rhat <<< (32 : BitVec 6).toNat) ||| un) h_inner
      -- div128Quot_phase2b_q0' q rhat dLo un = q + signExtend12 4095 when fire.
      have h_q1dd_eq : div128Quot_phase2b_q0' q rhat dLo un = q + signExtend12 4095 :=
        div128Quot_phase2b_q0'_eq_q_dec_of_fire q rhat dLo un h_outer h_inner
      rw [h_q1dd_eq]
      have h_se : (signExtend12 4095 : Word).toNat = 2^64 - 1 := by decide
      have h_q_dec : (q + signExtend12 4095).toNat = q.toNat - 1 := by
        rw [BitVec.toNat_add, h_se]
        have h_sum : q.toNat + (2^64 - 1) = (q.toNat - 1) + 2^64 := by omega
        rw [h_sum, Nat.add_mod_right]
        rw [Nat.mod_eq_of_lt (by have : q.toNat < 2^64 := q.isLt; omega)]
      rw [h_q_dec, h_no_wrap_rhat]
      -- Goal: (q - 1) * dHi + (rhat + dHi) = uHi
      -- = q * dHi - dHi + rhat + dHi = q * dHi + rhat = uHi.
      have h_rearrange :
          (q.toNat - 1) * dHi.toNat + (rhat.toNat + dHi.toNat) =
            q.toNat * dHi.toNat + rhat.toNat := by
        have hq_eq : q.toNat = (q.toNat - 1) + 1 := by omega
        calc
          (q.toNat - 1) * dHi.toNat + (rhat.toNat + dHi.toNat)
              = ((q.toNat - 1) * dHi.toNat + dHi.toNat) + rhat.toNat := by omega
            _ = ((q.toNat - 1) + 1) * dHi.toNat + rhat.toNat := by ring
            _ = q.toNat * dHi.toNat + rhat.toNat := by rw [← hq_eq]
      rw [h_rearrange]
      exact h_pre
    · -- No-fire BLTU: Q1dd = q, Rhatdd = rhat.
      rw [if_neg h_inner]
      have h_q1dd_eq : div128Quot_phase2b_q0' q rhat dLo un = q := by
        unfold div128Quot_phase2b_q0'
        rw [if_pos h_outer, if_neg h_inner]
      rw [h_q1dd_eq]
      exact h_pre
  · -- No-fire outer: Q1dd = q (phase2b_q0' guard fails), Rhatdd = rhat.
    rw [if_neg h_outer]
    have h_q1dd_eq : div128Quot_phase2b_q0' q rhat dLo un = q := by
      unfold div128Quot_phase2b_q0'
      rw [if_neg h_outer]
    rw [h_q1dd_eq]
    exact h_pre

/-- **V5.4.2 headline**: the V5 Phase-1b 2-correction quotient digit
    does not overshoot the abstract first 128/64 quotient digit. -/
theorem divKTrialCallV5Q1dd_le_q_true_1
    (uHi uLo vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63)
    (huHi_lt_vTop : uHi.toNat < vTop.toNat) :
    (divKTrialCallV5Q1dd uHi uLo vTop).toNat ≤
      (uHi.toNat * 2^32 + (divKTrialCallV5Un1 uLo).toNat) / vTop.toNat := by
  set q := divKTrialCallV5Q1dd uHi uLo vTop with hq
  set rhat := divKTrialCallV5Rhatdd uHi uLo vTop with hrhat
  set dHi := divKTrialCallV5DHi vTop with hdHi
  set dLo := divKTrialCallV5DLo vTop with hdLo
  set un1 := divKTrialCallV5Un1 uLo with hun1
  have h_vTop_decomp : vTop.toNat = dHi.toNat * 2^32 + dLo.toNat := by
    rw [hdHi, hdLo]; unfold divKTrialCallV5DHi divKTrialCallV5DLo
    exact div128Quot_vTop_decomp vTop
  have h_post : q.toNat * dHi.toNat + rhat.toNat = uHi.toNat := by
    rw [hq, hrhat, hdHi]
    exact divKTrialCallV5Q1dd_rhatdd_post uHi uLo vTop hvTop_ge
  have h_dLo_bound : q.toNat * dLo.toNat ≤ rhat.toNat * 2^32 + un1.toNat := by
    rw [hq, hrhat, hdLo, hun1]
    exact divKTrialCallV5_phase1b_dLo_bound uHi uLo vTop hvTop_ge huHi_lt_vTop
  have h_mul_le : q.toNat * vTop.toNat ≤ uHi.toNat * 2^32 + un1.toNat := by
    rw [h_vTop_decomp]
    calc q.toNat * (dHi.toNat * 2^32 + dLo.toNat)
        = q.toNat * dHi.toNat * 2^32 + q.toNat * dLo.toNat := by ring
      _ ≤ q.toNat * dHi.toNat * 2^32 + (rhat.toNat * 2^32 + un1.toNat) := by omega
      _ = (q.toNat * dHi.toNat + rhat.toNat) * 2^32 + un1.toNat := by ring
      _ = uHi.toNat * 2^32 + un1.toNat := by rw [h_post]
  have hvTop_pos : 0 < vTop.toNat := by omega
  exact (Nat.le_div_iff_mul_le hvTop_pos).2 h_mul_le

end EvmAsm.Evm64
