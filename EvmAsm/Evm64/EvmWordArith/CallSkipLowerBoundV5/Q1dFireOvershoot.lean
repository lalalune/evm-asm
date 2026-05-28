/-
  EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV5.Q1dFireOvershoot

  Fire-case overshoot bound at the V5 Phase-1b post-1st-correction:

    Q1d * dLo ≤ Rhatd * 2^32 + un1 + dHi * 2^32 + dLo

  Composes V5.4.0.16 (Q1d ≤ q_true_1 + 1 in fire) + V5.4.0.12 (Q1d
  Euclidean) algebraically:
  - Q1d ≤ q_true_1 + 1 ⇒ Q1d * vTop ≤ uHi*2^32 + un1 + vTop.
  - Q1d Euclidean ⇒ Q1d * dHi + Rhatd = uHi at Nat level.
  - vTop = dHi*2^32 + dLo decomposition + Q1d*vTop expansion gives the
    overshoot bound after Nat rearrangement.

  Mirror of v4's `algorithmQ1dV4_dLo_overshoot_le_vTop_of_phase1b_fire`
  (`Phase1bBound.lean:711`). Used by V5.4.1 case-split (with V5.4.0.10
  for the no-fire branch) to discharge the phase2b-fire-case helper's
  precondition.

  Bead `evm-asm-wbc4i.4.6.10` (V5.4.0.11). Prerequisite for V5.4.1.
-/

import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV5.Q1dKnuthAFire

namespace EvmAsm.Evm64

open EvmAsm.Rv64

theorem algorithmQ1dV5_dLo_overshoot_le_vTop_of_phase1b_fire
    (uHi uLo vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63)
    (huHi_lt_vTop : uHi.toNat < vTop.toNat)
    (h_fire : algorithmPhase1bFireV5 uHi uLo vTop) :
    (algorithmQ1dV5 uHi uLo vTop).toNat * (divKTrialCallV5DLo vTop).toNat ≤
      (algorithmRhatdV5 uHi uLo vTop).toNat * 2^32 +
        (divKTrialCallV5Un1 uLo).toNat +
        (divKTrialCallV5DHi vTop).toNat * 2^32 +
        (divKTrialCallV5DLo vTop).toNat := by
  -- Knuth-A fire-case bound: Q1d ≤ q_true_1 + 1.
  have h_q1d_le : (algorithmQ1dV5 uHi uLo vTop).toNat ≤
      (uHi.toNat * 2^32 + (divKTrialCallV5Un1 uLo).toNat) / vTop.toNat + 1 :=
    algorithmQ1dV5_le_qtrue_plus_one_of_phase1b_fire uHi uLo vTop
      hvTop_ge huHi_lt_vTop h_fire
  -- Q1d Euclidean: Q1d * dHi + Rhatd = uHi.
  have h_eucl : (algorithmQ1dV5 uHi uLo vTop).toNat *
        (divKTrialCallV5DHi vTop).toNat +
      (algorithmRhatdV5 uHi uLo vTop).toNat = uHi.toNat :=
    algorithmQ1dV5_rhatd_post uHi uLo vTop hvTop_ge
  -- vTop = dHi * 2^32 + dLo.
  have h_vTop : vTop.toNat =
      (divKTrialCallV5DHi vTop).toNat * 2^32 +
        (divKTrialCallV5DLo vTop).toNat := by
    unfold divKTrialCallV5DHi divKTrialCallV5DLo
    exact div128Quot_vTop_decomp vTop
  -- vTop ≥ 1 (from normalization).
  have h_vTop_pos : vTop.toNat ≥ 1 := by omega
  -- q_true_1 * vTop ≤ uHi*2^32 + un1.
  have h_qtrue_mul : ((uHi.toNat * 2^32 + (divKTrialCallV5Un1 uLo).toNat) /
        vTop.toNat) * vTop.toNat ≤ uHi.toNat * 2^32 +
      (divKTrialCallV5Un1 uLo).toNat := Nat.div_mul_le_self _ _
  -- Q1d * vTop ≤ uHi*2^32 + un1 + vTop.
  have h_q1d_vTop : (algorithmQ1dV5 uHi uLo vTop).toNat * vTop.toNat ≤
      uHi.toNat * 2^32 + (divKTrialCallV5Un1 uLo).toNat + vTop.toNat := by
    have h_mul_le : (algorithmQ1dV5 uHi uLo vTop).toNat * vTop.toNat ≤
        ((uHi.toNat * 2^32 + (divKTrialCallV5Un1 uLo).toNat) / vTop.toNat + 1) *
          vTop.toNat := Nat.mul_le_mul_right _ h_q1d_le
    have h_expand :
        ((uHi.toNat * 2^32 + (divKTrialCallV5Un1 uLo).toNat) / vTop.toNat + 1) *
          vTop.toNat =
        ((uHi.toNat * 2^32 + (divKTrialCallV5Un1 uLo).toNat) / vTop.toNat) *
          vTop.toNat + vTop.toNat := by ring
    omega
  -- Substitute vTop expansion to get Q1d * dHi * 2^32 + Q1d * dLo ≤ ...
  have h_q1d_split : (algorithmQ1dV5 uHi uLo vTop).toNat * vTop.toNat =
      (algorithmQ1dV5 uHi uLo vTop).toNat *
        (divKTrialCallV5DHi vTop).toNat * 2^32 +
      (algorithmQ1dV5 uHi uLo vTop).toNat *
        (divKTrialCallV5DLo vTop).toNat := by
    rw [h_vTop]; ring
  -- From Euclidean: Q1d * dHi = uHi - Rhatd (with Rhatd ≤ uHi).
  have h_rhatd_le_uHi : (algorithmRhatdV5 uHi uLo vTop).toNat ≤ uHi.toNat := by
    omega
  have h_q1d_dHi : (algorithmQ1dV5 uHi uLo vTop).toNat *
      (divKTrialCallV5DHi vTop).toNat =
      uHi.toNat - (algorithmRhatdV5 uHi uLo vTop).toNat := by omega
  -- Now Q1d * dLo = Q1d * vTop - Q1d * dHi * 2^32, and Q1d * dHi * 2^32 =
  -- (uHi - Rhatd) * 2^32 = uHi*2^32 - Rhatd*2^32.
  rw [h_vTop] at h_q1d_vTop
  -- Goal restated using h_q1d_split, h_q1d_dHi, and h_q1d_vTop.
  have h_q1d_dHi_pow32 :
      (algorithmQ1dV5 uHi uLo vTop).toNat *
        (divKTrialCallV5DHi vTop).toNat * 2^32 =
      uHi.toNat * 2^32 - (algorithmRhatdV5 uHi uLo vTop).toNat * 2^32 := by
    rw [h_q1d_dHi]; rw [Nat.sub_mul]
  have h_rhatd_pow32_le : (algorithmRhatdV5 uHi uLo vTop).toNat * 2^32 ≤
      uHi.toNat * 2^32 := Nat.mul_le_mul_right _ h_rhatd_le_uHi
  -- Set up abbreviations and key linear facts.
  set Q := (algorithmQ1dV5 uHi uLo vTop).toNat
  set R := (algorithmRhatdV5 uHi uLo vTop).toNat
  set D := (divKTrialCallV5DHi vTop).toNat
  set L := (divKTrialCallV5DLo vTop).toNat
  set U := uHi.toNat
  set U1 := (divKTrialCallV5Un1 uLo).toNat
  -- h_q1d_vTop is already in the form `Q*(D*2^32+L) ≤ ...` after the earlier rw [h_vTop].
  -- Expand Q * (D*2^32 + L) = Q*D*2^32 + Q*L.
  have h_expand : Q * (D * 2^32 + L) = Q * D * 2^32 + Q * L := by ring
  have h_QD : Q * D * 2^32 = U * 2^32 - R * 2^32 := h_q1d_dHi_pow32
  have h_R_pow32 : R * 2^32 ≤ U * 2^32 := h_rhatd_pow32_le
  -- Goal: Q * L ≤ R * 2^32 + U1 + D * 2^32 + L.
  linarith [h_q1d_vTop, h_expand, h_QD, h_R_pow32]

end EvmAsm.Evm64
