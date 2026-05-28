/-
  EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV5.Q1dEuclidean

  Phase-1b Euclidean identity at the V5 post-1st-correction level:
  `Q1d * dHi + Rhatd = uHi`. Holds unconditionally via case analysis:
  - No-fire: Q1d = Q1c, Rhatd = Rhatc; reduce to `algorithmQ1cV5_rhatc_post`.
  - Fire: Q1d = Q1c - 1 (Word, with no-wrap from Q1c ≥ 1 derived from BLTU),
    Rhatd = Rhatc + dHi (with no-wrap from rhatc >>> 32 = 0 ⇒ Rhatc < 2^32);
    algebra cancels and reduces to the Q1c Euclidean identity.

  Mirror of v4's `algorithmQ1dV4_rhatd_post` (`Phase1bBound.lean:113`).

  Bead `evm-asm-wbc4i.4.6.11` (V5.4.0.12). Prerequisite for V5.4.0.11 (fire-case
  overshoot) and V5.4.1.
-/

import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV5.Q1dNoFire

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- When Phase-1b 1st correction fires, the BLTU subterm implies
    `Q1c.toNat ≥ 1` (since `BLTU x 0 = false` for any unsigned `x`). -/
private theorem q1c_pos_of_phase1b_fire
    (uHi uLo vTop : Word)
    (h_fire : algorithmPhase1bFireV5 uHi uLo vTop) :
    (algorithmQ1cV5 uHi vTop).toNat ≥ 1 := by
  delta algorithmPhase1bFireV5 algorithmRhatUn1cV5 at h_fire
  obtain ⟨_, h_ult⟩ := h_fire
  by_contra hq_lt
  push Not at hq_lt
  have hq_nat : (algorithmQ1cV5 uHi vTop).toNat = 0 := by omega
  have hq0 : algorithmQ1cV5 uHi vTop = 0 := BitVec.eq_of_toNat_eq hq_nat
  rw [hq0] at h_ult
  simp [BitVec.ult] at h_ult

/-- When Phase-1b 1st correction fires, `rhatc >>> 32 = 0` (the guard half
    of `algorithmPhase1bFireV5`), and hence `Rhatc < 2^32`. -/
private theorem rhatc_lt_pow32_of_phase1b_fire
    (uHi uLo vTop : Word)
    (h_fire : algorithmPhase1bFireV5 uHi uLo vTop) :
    (algorithmRhatcV5 uHi vTop).toNat < 2^32 := by
  delta algorithmPhase1bFireV5 algorithmRhatUn1cV5 at h_fire
  obtain ⟨h_hi_zero, _⟩ := h_fire
  -- rhatc >>> 32 = 0 ⇒ rhatc.toNat / 2^32 = 0 ⇒ rhatc.toNat < 2^32
  have h_nat : (algorithmRhatcV5 uHi vTop >>> (32 : BitVec 6).toNat).toNat = 0 := by
    rw [h_hi_zero]; rfl
  rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32,
      Nat.shiftRight_eq_div_pow] at h_nat
  have h_lt : (algorithmRhatcV5 uHi vTop).toNat < 2^64 :=
    (algorithmRhatcV5 uHi vTop).isLt
  exact Nat.div_eq_zero_iff.mp h_nat |>.resolve_left (by decide)

/-- The V5 Phase-1b post-1st-correction Euclidean identity. -/
theorem algorithmQ1dV5_rhatd_post
    (uHi uLo vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63) :
    (algorithmQ1dV5 uHi uLo vTop).toNat * (divKTrialCallV5DHi vTop).toNat +
      (algorithmRhatdV5 uHi uLo vTop).toNat = uHi.toNat := by
  have h_pre := algorithmQ1cV5_rhatc_post uHi vTop hvTop_ge
  by_cases h_fire : algorithmPhase1bFireV5 uHi uLo vTop
  · -- Fire: Q1d = Q1c + signExtend12 4095, Rhatd = Rhatc + dHi.
    rw [algorithmQ1dV5_unfold, algorithmRhatdV5_unfold]
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
    rw [if_pos h_fire_cond, if_pos h_fire_cond]
    -- Need: (Q1c + sx 4095).toNat * dHi + (Rhatc + dHi).toNat = uHi.toNat
    set q1c := algorithmQ1cV5 uHi vTop with hq1c
    set rhatc := algorithmRhatcV5 uHi vTop with hrhatc
    set dHi := divKTrialCallV5DHi vTop with hdHi
    -- Q1c ≥ 1 from fire (BLTU on q1c*dLo ≠ 0)
    have h_q1c_pos : q1c.toNat ≥ 1 := by
      rw [hq1c]; exact q1c_pos_of_phase1b_fire uHi uLo vTop h_fire
    -- Q1c < 2^32 from cap
    have h_q1c_lt : q1c.toNat < 2^32 := by
      rw [hq1c]; exact algorithmQ1cV5_lt_pow32 uHi vTop
    -- Rhatc < 2^32 from fire's high-half guard
    have h_rhatc_lt : rhatc.toNat < 2^32 := by
      rw [hrhatc]; exact rhatc_lt_pow32_of_phase1b_fire uHi uLo vTop h_fire
    -- dHi < 2^32
    have h_dHi_lt : dHi.toNat < 2^32 := by
      rw [hdHi]; exact divKTrialCallV5DHi_lt_pow32 vTop
    -- (Q1c + signExtend12 4095).toNat = Q1c.toNat - 1 (no-wrap since Q1c ≥ 1)
    have h_se : (signExtend12 4095 : Word).toNat = 2^64 - 1 := by decide
    have h_q1d_eq : (q1c + signExtend12 4095).toNat = q1c.toNat - 1 := by
      rw [BitVec.toNat_add, h_se]
      have h_sum : q1c.toNat + (2^64 - 1) = (q1c.toNat - 1) + 2^64 := by omega
      rw [h_sum, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : q1c.toNat - 1 < 2^64)]
    -- (Rhatc + dHi).toNat = Rhatc.toNat + dHi.toNat (no-wrap since both < 2^32)
    have h_rhatd_eq : (rhatc + dHi).toNat = rhatc.toNat + dHi.toNat := by
      rw [BitVec.toNat_add]
      apply Nat.mod_eq_of_lt; omega
    rw [h_q1d_eq, h_rhatd_eq]
    -- Need: (Q1c - 1) * dHi + (Rhatc + dHi) = Q1c * dHi + Rhatc = uHi.toNat
    have h_q1c_dHi : q1c.toNat * dHi.toNat = (q1c.toNat - 1) * dHi.toNat + dHi.toNat := by
      have : q1c.toNat = (q1c.toNat - 1) + 1 := by omega
      calc q1c.toNat * dHi.toNat
          = ((q1c.toNat - 1) + 1) * dHi.toNat := by rw [← this]
        _ = (q1c.toNat - 1) * dHi.toNat + dHi.toNat := by ring
    have h_pre' : q1c.toNat * dHi.toNat + rhatc.toNat = uHi.toNat := by
      rw [hq1c, hdHi, hrhatc] at *; exact h_pre
    omega
  · -- No-fire: Q1d = Q1c, Rhatd = Rhatc.
    rw [algorithmQ1dV5_eq_q1c_of_phase1b_no_fire uHi uLo vTop h_fire,
        algorithmRhatdV5_eq_rhatc_of_phase1b_no_fire uHi uLo vTop h_fire]
    exact h_pre

/-- The product `Q1d * dLo` does not wrap mod 2^64 under the V5 cap.
    Trivial consequence of `Q1d < 2^32` (V5.4.0.6) and `dLo < 2^32`
    (V5.4.0.5). Used by V5.4.1 when bridging the Phase-1b 2nd
    correction's word-level BLTU to the Nat-level dLo bound. -/
theorem algorithmQ1dV5_dLo_no_wrap (uHi uLo vTop : Word) :
    (algorithmQ1dV5 uHi uLo vTop * divKTrialCallV5DLo vTop).toNat =
      (algorithmQ1dV5 uHi uLo vTop).toNat * (divKTrialCallV5DLo vTop).toNat := by
  rw [BitVec.toNat_mul]
  apply Nat.mod_eq_of_lt
  have h_q := algorithmQ1dV5_lt_pow32 uHi uLo vTop
  have h_d := divKTrialCallV5DLo_lt_pow32 vTop
  have : (algorithmQ1dV5 uHi uLo vTop).toNat * (divKTrialCallV5DLo vTop).toNat <
      2^32 * 2^32 := Nat.mul_lt_mul'' h_q h_d
  calc (algorithmQ1dV5 uHi uLo vTop).toNat * (divKTrialCallV5DLo vTop).toNat
      < 2^32 * 2^32 := this
    _ = 2^64 := by norm_num

end EvmAsm.Evm64
