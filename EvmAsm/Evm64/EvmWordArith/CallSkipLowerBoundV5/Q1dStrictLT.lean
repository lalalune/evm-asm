/-
  EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV5.Q1dStrictLT

  V5.5.0.5: when V5's Phase-1b 2nd correction fires, the abstract first
  quotient digit is STRICTLY less than the post-1st-correction quotient
  Q1d.

  Mirror of v4's `algorithmQ1dV4_q_true_1_lt_of_phase2b_fire`
  (`CallSkipLowerBoundV4/Phase1bBound.lean:1161`).

  Bead `evm-asm-wbc4i.5.8` (V5.5.0.5). Prerequisite for V5.5.1 to show
  Q1dd = Q1d - 1 ≥ q_true_1 in the 2nd-correction fire case.
-/

import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV5.Q1dLB

namespace EvmAsm.Evm64

open EvmAsm.Rv64 EvmWord

theorem algorithmQ1dV5_q_true_1_lt_of_phase2b_fire
    (uHi uLo vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63)
    (h_rhat_hi_zero :
      algorithmRhatdV5 uHi uLo vTop >>> (32 : BitVec 6).toNat = (0 : Word))
    (h_ult :
      BitVec.ult ((algorithmRhatdV5 uHi uLo vTop <<< (32 : BitVec 6).toNat) |||
          divKTrialCallV5Un1 uLo)
        (algorithmQ1dV5 uHi uLo vTop * divKTrialCallV5DLo vTop)) :
    (uHi.toNat * 2^32 + (divKTrialCallV5Un1 uLo).toNat) / vTop.toNat <
      (algorithmQ1dV5 uHi uLo vTop).toNat := by
  set q := algorithmQ1dV5 uHi uLo vTop with hq
  set rhat := algorithmRhatdV5 uHi uLo vTop with hrhat
  set dHi := divKTrialCallV5DHi vTop with hdHi
  set dLo := divKTrialCallV5DLo vTop with hdLo
  set un := divKTrialCallV5Un1 uLo with hun
  -- vTop decomposition.
  have h_vTop_decomp : vTop.toNat = dHi.toNat * 2^32 + dLo.toNat := by
    rw [hdHi, hdLo]; unfold divKTrialCallV5DHi divKTrialCallV5DLo
    exact div128Quot_vTop_decomp vTop
  -- Q1d Euclidean (V5.4.0.12).
  have h_post : q.toNat * dHi.toNat + rhat.toNat = uHi.toNat := by
    rw [hq, hrhat, hdHi]
    exact algorithmQ1dV5_rhatd_post uHi uLo vTop hvTop_ge
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
  -- (q * dLo).toNat = q * dLo (V5.4.0.13).
  have h_rhs_toNat : (q * dLo).toNat = q.toNat * dLo.toNat := by
    rw [hq, hdLo]; exact algorithmQ1dV5_dLo_no_wrap uHi uLo vTop
  -- BLTU → Nat-level <.
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
