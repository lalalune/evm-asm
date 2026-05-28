/-
  EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV5.Q1cStrictLT

  V5.5.0.3: when V5's Phase-1b 1st correction fires, the abstract first
  quotient digit is STRICTLY less than the Phase-1a-corrected quotient:

    algorithmPhase1bFireV5 ⇒ q_true_1 < Q1c.toNat

  Uses the generic `phase1b_fire_q_true_1_lt_q_nat` helper from
  `CallSkipLowerBoundV4/Phase1bBound.lean` + Q1c Euclidean (V5.4.0.7)
  + bit-level no-wrap facts.

  Bead `evm-asm-wbc4i.5.6` (V5.5.0.3). Prerequisite for V5.5.1 to show
  Q1d = Q1c - 1 ≥ q_true_1 in the fire case.
-/

import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV5.Q1cLBUncond
import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV4.Phase1bBound

namespace EvmAsm.Evm64

open EvmAsm.Rv64 EvmWord

theorem algorithmQ1cV5_q_true_1_lt_of_phase1b_fire
    (uHi uLo vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63)
    (h_fire : algorithmPhase1bFireV5 uHi uLo vTop) :
    (uHi.toNat * 2^32 + (divKTrialCallV5Un1 uLo).toNat) / vTop.toNat <
      (algorithmQ1cV5 uHi vTop).toNat := by
  -- Extract fire's two conditions.
  rw [algorithmPhase1bFireV5_unfold] at h_fire
  rw [algorithmRhatUn1cV5_unfold] at h_fire
  obtain ⟨h_rhat_hi_zero, h_ult⟩ := h_fire
  -- Setup names.
  set q := algorithmQ1cV5 uHi vTop with hq
  set rhat := algorithmRhatcV5 uHi vTop with hrhat
  set dHi := divKTrialCallV5DHi vTop with hdHi
  set dLo := divKTrialCallV5DLo vTop with hdLo
  set un := divKTrialCallV5Un1 uLo with hun
  -- Get vTop decomposition.
  have h_vTop_decomp : vTop.toNat = dHi.toNat * 2^32 + dLo.toNat := by
    rw [hdHi, hdLo]; unfold divKTrialCallV5DHi divKTrialCallV5DLo
    exact div128Quot_vTop_decomp vTop
  -- Get Q1c Euclidean (V5.4.0.7): q * dHi + rhat = uHi.
  have h_post : q.toNat * dHi.toNat + rhat.toNat = uHi.toNat := by
    rw [hq, hrhat, hdHi]
    exact algorithmQ1cV5_rhatc_post uHi vTop hvTop_ge
  -- rhat < 2^32 from h_rhat_hi_zero.
  have h_rhat_lt : rhat.toNat < 2^32 := by
    have h_nat : (rhat >>> (32 : BitVec 6).toNat).toNat = 0 := by
      rw [h_rhat_hi_zero]; rfl
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32,
        Nat.shiftRight_eq_div_pow] at h_nat
    have : rhat.toNat < 2^64 := rhat.isLt
    omega
  have h_un_lt : un.toNat < 2^32 := by
    rw [hun]; exact divKTrialCallV5Un1_lt_pow32 uLo
  -- (rhat <<< 32 ||| un).toNat = rhat * 2^32 + un.
  have h_lhs_toNat :
      (((rhat <<< (32 : BitVec 6).toNat) ||| un).toNat) =
        rhat.toNat * 2^32 + un.toNat := by
    rw [show ((32 : BitVec 6).toNat : Nat) = 32 from by rfl]
    exact halfword_combine rhat un h_rhat_lt h_un_lt
  -- (q * dLo).toNat = q * dLo (no-wrap, V5.4.0.5).
  have h_rhs_toNat : (q * dLo).toNat = q.toNat * dLo.toNat := by
    rw [hq, hdLo]; exact algorithmQ1cV5_dLo_no_wrap uHi vTop
  -- Convert BLTU to Nat-level <.
  have h_ult_nat :
      rhat.toNat * 2^32 + un.toNat < q.toNat * dLo.toNat := by
    have h_word : ((rhat <<< (32 : BitVec 6).toNat) ||| un).toNat <
        (q * dLo).toNat := by
      simpa [BitVec.ult, hq, hrhat, hdLo, hun] using h_ult
    rw [h_lhs_toNat, h_rhs_toNat] at h_word
    exact h_word
  -- Apply generic phase1b_fire_q_true_1_lt_q_nat.
  have h_core := phase1b_fire_q_true_1_lt_q_nat
    uHi.toNat un.toNat dHi.toNat dLo.toNat q.toNat rhat.toNat
    (by rw [← h_vTop_decomp]; omega)
    h_post h_ult_nat
  rw [← h_vTop_decomp] at h_core
  exact h_core

end EvmAsm.Evm64
