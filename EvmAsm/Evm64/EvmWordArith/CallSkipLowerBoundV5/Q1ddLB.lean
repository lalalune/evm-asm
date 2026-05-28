/-
  EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV5.Q1ddLB

  **V5.5.1 headline**: the V5 post-Phase-1b-2nd-correction quotient does
  not undershoot the abstract first 128/64 quotient digit:

    Q1dd.toNat ≥ q_true_1

  Unconditional under `vTop ≥ 2^63` and `uHi < vTop` (no `uHi < 2^63`
  exclusion — the V5 cap eliminates v4's wide-uHi counterexamples from
  PR #7077).

  Compose:
  - V5.5.0.4 (Q1d ≥ q_true_1).
  - V5.5.0.5 (2nd-fire ⇒ q_true_1 < Q1d strict) for the fire case.
  - V5.4.1.1 bridges (`divKTrialCallV5{Q1dd,Rhatdd}_eq_alg`) to lift to
    irreducible form.

  Mirror of v4's `divKTrialCallV4Q1dd_ge_q_true_1_of_uHi_lt_pow63`
  (`CallSkipLowerBoundV4/Phase1bBound.lean:1213`) but STRONGER: V5
  drops the `uHi < 2^63` precondition.

  Bead `evm-asm-wbc4i.5.1` (V5.5.1).
-/

import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV5.Q1dStrictLT
import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV5.Phase1bBound

namespace EvmAsm.Evm64

open EvmAsm.Rv64

theorem divKTrialCallV5Q1dd_ge_q_true_1
    (uHi uLo vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63)
    (huHi_lt_vTop : uHi.toNat < vTop.toNat) :
    (uHi.toNat * 2^32 + (divKTrialCallV5Un1 uLo).toNat) / vTop.toNat ≤
      (divKTrialCallV5Q1dd uHi uLo vTop).toNat := by
  -- Q1d ≥ q_true_1 unconditionally (V5.5.0.4).
  have h_q1d_ge : (uHi.toNat * 2^32 + (divKTrialCallV5Un1 uLo).toNat) /
      vTop.toNat ≤ (algorithmQ1dV5 uHi uLo vTop).toNat :=
    algorithmQ1dV5_ge_q_true_1 uHi uLo vTop hvTop_ge huHi_lt_vTop
  -- Bridge: divKTrialCallV5Q1dd = div128Quot_phase2b_q0' Q1d Rhatd dLo un.
  rw [divKTrialCallV5Q1dd_eq_alg]
  set q := algorithmQ1dV5 uHi uLo vTop with hq
  set rhat := algorithmRhatdV5 uHi uLo vTop with hrhat
  set dLo := divKTrialCallV5DLo vTop with hdLo
  set un := divKTrialCallV5Un1 uLo with hun
  set qTrue := (uHi.toNat * 2^32 + (divKTrialCallV5Un1 uLo).toNat) / vTop.toNat
    with hqTrue
  -- Case-split on the 2nd correction guard.
  by_cases h_outer : rhat >>> (32 : BitVec 6).toNat = (0 : Word)
  · by_cases h_inner :
        BitVec.ult ((rhat <<< (32 : BitVec 6).toNat) ||| un) (q * dLo)
    · -- 2nd correction FIRES: phase2b_q0' = q + signExtend12 4095 = q - 1.
      have h_q1dd_eq : div128Quot_phase2b_q0' q rhat dLo un = q + signExtend12 4095 :=
        div128Quot_phase2b_q0'_eq_q_dec_of_fire q rhat dLo un h_outer h_inner
      rw [h_q1dd_eq]
      -- Strict overshoot (V5.5.0.5): q_true_1 < Q1d.
      have h_strict : qTrue < q.toNat := by
        rw [hqTrue, hq]
        exact algorithmQ1dV5_q_true_1_lt_of_phase2b_fire uHi uLo vTop
          hvTop_ge h_outer h_inner
      -- Q1d < 2^32 (V5.4.0.6).
      have h_q_lt : q.toNat < 2^32 := by
        rw [hq]; exact algorithmQ1dV5_lt_pow32 uHi uLo vTop
      have h_q_pos : q.toNat ≥ 1 :=
        Nat.one_le_iff_ne_zero.mpr (fun h => by
          rw [h] at h_strict; exact Nat.not_lt_zero _ h_strict)
      -- (q + signExtend12 4095).toNat = q.toNat - 1 mod 2^64 (no-wrap).
      have h_se : (signExtend12 4095 : Word).toNat = 2^64 - 1 := by decide
      rw [BitVec.toNat_add, h_se]
      have h_sum : q.toNat + (2^64 - 1) = (q.toNat - 1) + 2^64 := by omega
      have h_lt_pow64 : q.toNat - 1 < 2^64 := by
        have h32 : (2 : Nat)^32 < 2^64 := by decide
        omega
      rw [h_sum, Nat.add_mod_right, Nat.mod_eq_of_lt h_lt_pow64]
      exact Nat.le_sub_one_of_lt h_strict
    · -- 2nd correction doesn't fire (BLTU false): phase2b_q0' = q.
      have h_q1dd_eq : div128Quot_phase2b_q0' q rhat dLo un = q := by
        unfold div128Quot_phase2b_q0'
        rw [if_pos h_outer, if_neg h_inner]
      rw [h_q1dd_eq]
      exact h_q1d_ge
  · -- Outer guard false: phase2b_q0' = q.
    have h_q1dd_eq : div128Quot_phase2b_q0' q rhat dLo un = q := by
      unfold div128Quot_phase2b_q0'
      rw [if_neg h_outer]
    rw [h_q1dd_eq]
    exact h_q1d_ge

end EvmAsm.Evm64
