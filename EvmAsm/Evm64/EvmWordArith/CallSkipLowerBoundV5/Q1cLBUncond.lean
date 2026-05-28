/-
  EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV5.Q1cLBUncond

  V5.5.0.2: unconditional Knuth-A lower bound for V5's Phase-1a-corrected
  quotient: `Q1c ≥ q_true_1`.

  Case-split on `hi1 = q1 >>> 32`:
  - `hi1 = 0` (narrow uHi): Q1c = q1; use existing `div128Quot_q1c_ge_q_true_1`
    from `Div128KnuthLower.lean` (which holds for q1 - 1 form, but the
    narrow branch is q1 in both forms).
  - `hi1 ≠ 0` (wide uHi, ≥ dHi*2^32): use V5.5.0.1.

  Bead `evm-asm-wbc4i.5.5` (V5.5.0.2). Prerequisite for V5.5.1.
-/

import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV5.Q1cLB
import EvmAsm.Evm64.EvmWordArith.Div128KnuthLower

namespace EvmAsm.Evm64

open EvmAsm.Rv64

theorem algorithmQ1cV5_ge_q_true_1
    (uHi uLo vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63)
    (huHi_lt_vTop : uHi.toNat < vTop.toNat) :
    (uHi.toNat * 2^32 + (divKTrialCallV5Un1 uLo).toNat) / vTop.toNat ≤
      (algorithmQ1cV5 uHi vTop).toNat := by
  have h_dHi_lt : (divKTrialCallV5DHi vTop).toNat < 2^32 :=
    divKTrialCallV5DHi_lt_pow32 vTop
  have h_dHi_ge : (divKTrialCallV5DHi vTop).toNat ≥ 2^31 := by
    unfold divKTrialCallV5DHi
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    omega
  have h_dHi_ne : divKTrialCallV5DHi vTop ≠ 0 := by
    intro h
    have : (divKTrialCallV5DHi vTop).toNat = 0 := by rw [h]; rfl
    omega
  have h_un1_lt : (divKTrialCallV5Un1 uLo).toNat < 2^32 :=
    divKTrialCallV5Un1_lt_pow32 uLo
  have h_vTop_decomp : vTop.toNat =
      (divKTrialCallV5DHi vTop).toNat * 2^32 +
        (divKTrialCallV5DLo vTop).toNat := by
    unfold divKTrialCallV5DHi divKTrialCallV5DLo
    exact div128Quot_vTop_decomp vTop
  by_cases h_wide : uHi.toNat ≥ (divKTrialCallV5DHi vTop).toNat * 2^32
  · -- Wide case: V5.5.0.1.
    exact algorithmQ1cV5_ge_q_true_1_of_uHi_ge_dHi_pow32 uHi uLo vTop
      hvTop_ge huHi_lt_vTop h_wide
  · -- Narrow case: Q1c = q1, use the existing Div128KnuthLower fact.
    push Not at h_wide
    have h_uHi_lt_decomp : uHi.toNat <
        (divKTrialCallV5DHi vTop).toNat * 2^32 +
          (divKTrialCallV5DLo vTop).toNat := by
      rw [← h_vTop_decomp]; exact huHi_lt_vTop
    -- div128Quot_q1c_ge_q_true_1 uses v2's cap form (q1 - 1), but in the
    -- narrow case (hi1 = 0), both v2 and V5 caps reduce to q1c = q1.
    have h_q1_ge :
        (uHi.toNat * 2^32 + (divKTrialCallV5Un1 uLo).toNat) /
          ((divKTrialCallV5DHi vTop).toNat * 2^32 +
            (divKTrialCallV5DLo vTop).toNat) ≤
        (rv64_divu uHi (divKTrialCallV5DHi vTop)).toNat := by
      exact div128Quot_q1_ge_q_true_1 uHi (divKTrialCallV5DHi vTop)
        (divKTrialCallV5DLo vTop) (divKTrialCallV5Un1 uLo)
        h_dHi_ne h_un1_lt
    rw [h_vTop_decomp]
    -- Need: q_true_1 ≤ Q1c.toNat. We have q_true_1 ≤ q1.toNat. Show Q1c = q1
    -- when hi1 = 0 (which follows from h_wide_neg : uHi < dHi*2^32).
    have h_q1_eq : (rv64_divu uHi (divKTrialCallV5DHi vTop)).toNat =
        uHi.toNat / (divKTrialCallV5DHi vTop).toNat := by
      unfold rv64_divu
      have : ¬ (divKTrialCallV5DHi vTop == 0#64) := by simpa using h_dHi_ne
      rw [if_neg this, BitVec.toNat_udiv]
    have h_q1_lt : (rv64_divu uHi (divKTrialCallV5DHi vTop)).toNat < 2^32 := by
      rw [h_q1_eq]
      exact Nat.div_lt_of_lt_mul (by linarith)
    have h_hi1_zero : rv64_divu uHi (divKTrialCallV5DHi vTop) >>>
        (32 : BitVec 6).toNat = (0 : Word) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32,
          Nat.shiftRight_eq_div_pow]
      show (rv64_divu uHi (divKTrialCallV5DHi vTop)).toNat / 2^32 = 0
      exact Nat.div_eq_of_lt h_q1_lt
    -- Q1c = q1 in narrow case.
    have h_q1c_eq : (algorithmQ1cV5 uHi vTop).toNat =
        (rv64_divu uHi (divKTrialCallV5DHi vTop)).toNat := by
      rw [algorithmQ1cV5_unfold]
      dsimp only
      rw [if_pos h_hi1_zero]
    rw [h_q1c_eq]
    exact h_q1_ge

end EvmAsm.Evm64
