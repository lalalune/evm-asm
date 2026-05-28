/-
  EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV5.Un21Bound

  V5.4.3 prereq: `Q1dd * dLo` no-wrap helper at the irreducible level
  (lifts V5.4.0.13's algorithm-level no-wrap through the
  `div128Quot_phase2b_q0'` step).

  V5.4.3 (`divKTrialCallV5Un21 < vTop`) itself has a non-trivial proof
  via the algebraic identity `un21 = (uHi*2^32 + un1) - Q1dd*vTop`,
  which equals `(uHi*2^32 + un1) mod vTop` when `Q1dd = q_true_1`
  (V5.5.0.6). The BitVec `Rhatdd << 32` truncation doesn't break the
  identity because the truncated bits represent `Rhatdd div 2^32 * 2^64`
  which is `0 mod 2^64`. Future iteration ships the headline; this PR
  lands the no-wrap step that the proof composition needs.

  Bead `evm-asm-wbc4i.4.3` (V5.4.3, no-wrap prereq).
-/

import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV5.Q1ddLB

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- `Q1dd * dLo` no-wrap at the irreducible level. Lifts V5.4.0.13's
    algorithm-level bound (Q1d * dLo ≤ Q1d * dLo < 2^32 * 2^32) through
    `div128Quot_phase2b_q0'`'s monotonicity (Q1dd ≤ Q1d). -/
theorem divKTrialCallV5Q1dd_dLo_no_wrap (uHi uLo vTop : Word) :
    (divKTrialCallV5Q1dd uHi uLo vTop * divKTrialCallV5DLo vTop).toNat =
      (divKTrialCallV5Q1dd uHi uLo vTop).toNat *
        (divKTrialCallV5DLo vTop).toNat := by
  rw [BitVec.toNat_mul]
  apply Nat.mod_eq_of_lt
  -- Q1dd.toNat ≤ algorithmQ1dV5 (via phase2b_q0' monotonicity through
  -- the V5.4.1.1 bridge); algorithmQ1dV5 < 2^32; dLo < 2^32.
  rw [divKTrialCallV5Q1dd_eq_alg]
  have h_q1d_lt : (algorithmQ1dV5 uHi uLo vTop).toNat < 2^32 :=
    algorithmQ1dV5_lt_pow32 uHi uLo vTop
  have h_dLo_lt : (divKTrialCallV5DLo vTop).toNat < 2^32 :=
    divKTrialCallV5DLo_lt_pow32 vTop
  -- div128Quot_phase2b_q0' q rhat dLo un ≤ q at Nat level.
  -- Generic helper-style: phase2b_q0' is either q or q + signExtend12 4095.
  have h_phase2b_le :
      ∀ (q rhat dLo un : Word),
      (div128Quot_phase2b_q0' q rhat dLo un).toNat ≤ q.toNat := by
    intro q rhat dLo un
    unfold div128Quot_phase2b_q0'
    by_cases h_outer : rhat >>> (32 : BitVec 6).toNat = (0 : Word)
    · rw [if_pos h_outer]
      by_cases h_inner : BitVec.ult ((rhat <<< (32 : BitVec 6).toNat) ||| un) (q * dLo)
      · simp only [h_inner, ↓reduceIte]
        rw [BitVec.toNat_add]
        have h_se : (signExtend12 4095 : Word).toNat = 2^64 - 1 := by decide
        rw [h_se]
        by_cases hq : q.toNat = 0
        · -- q = 0 contradicts fire: BLTU x 0 = false for any x.
          exfalso
          have h_q_eq : q = 0 := BitVec.eq_of_toNat_eq hq
          have h_mul_zero : q * dLo = 0 := by rw [h_q_eq]; exact BitVec.zero_mul
          rw [h_mul_zero] at h_inner
          simp [BitVec.ult] at h_inner
        · have h_pos : q.toNat ≥ 1 := Nat.one_le_iff_ne_zero.mpr hq
          have h_sum : q.toNat + (2^64 - 1) = (q.toNat - 1) + 2^64 := by omega
          rw [h_sum, Nat.add_mod_right,
              Nat.mod_eq_of_lt (by have : q.toNat < 2^64 := q.isLt; omega)]
          omega
      · simp only [h_inner, ↓reduceIte, Bool.false_eq_true]
        rfl
    · rw [if_neg h_outer]
  have h_phase2b_q1d := h_phase2b_le (algorithmQ1dV5 uHi uLo vTop)
    (algorithmRhatdV5 uHi uLo vTop) (divKTrialCallV5DLo vTop)
    (divKTrialCallV5Un1 uLo)
  -- Compose: phase2b_q0' result ≤ algorithmQ1dV5 < 2^32, so product < 2^64.
  have h_mul_le :
      (div128Quot_phase2b_q0' (algorithmQ1dV5 uHi uLo vTop)
        (algorithmRhatdV5 uHi uLo vTop) (divKTrialCallV5DLo vTop)
        (divKTrialCallV5Un1 uLo)).toNat * (divKTrialCallV5DLo vTop).toNat ≤
      (algorithmQ1dV5 uHi uLo vTop).toNat * (divKTrialCallV5DLo vTop).toNat :=
    Nat.mul_le_mul_right _ h_phase2b_q1d
  have h_prod_bound :
      (algorithmQ1dV5 uHi uLo vTop).toNat * (divKTrialCallV5DLo vTop).toNat <
        2^32 * 2^32 := Nat.mul_lt_mul'' h_q1d_lt h_dLo_lt
  calc (div128Quot_phase2b_q0' (algorithmQ1dV5 uHi uLo vTop)
      (algorithmRhatdV5 uHi uLo vTop) (divKTrialCallV5DLo vTop)
      (divKTrialCallV5Un1 uLo)).toNat * (divKTrialCallV5DLo vTop).toNat
      ≤ (algorithmQ1dV5 uHi uLo vTop).toNat * (divKTrialCallV5DLo vTop).toNat :=
        h_mul_le
    _ < 2^32 * 2^32 := h_prod_bound
    _ = 2^64 := by norm_num

end EvmAsm.Evm64
