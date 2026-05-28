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

/-- Like `EvmWord.halfword_combine` but without the `a < 2^32` bound; the
    high word `a` is silently truncated to its low 32 bits. Used for the
    `Rhatdd <<< 32 ||| un1` combine when Rhatdd may be ≥ 2^32. -/
private theorem halfword_combine_truncated (a b : Word) (hb : b.toNat < 2^32) :
    (a <<< (32 : Nat) ||| b).toNat = (a.toNat % 2^32) * 2^32 + b.toNat := by
  have h_disj : a <<< (32 : Nat) &&& b = 0 := by
    ext i
    simp only [BitVec.getElem_and, BitVec.getElem_shiftLeft]
    by_cases hi : (i : Nat) < 32
    · simp [hi]
    · simp only [hi, decide_false, Bool.not_false, Bool.true_and]
      have hbi : b[i] = false := by
        simp only [BitVec.getElem_eq_testBit_toNat]
        apply Nat.testBit_lt_two_pow
        calc b.toNat < 2 ^ 32 := hb
          _ ≤ 2 ^ (i : Nat) := Nat.pow_le_pow_right (by omega) (by omega)
      simp [hbi]
  rw [(BitVec.add_eq_or_of_and_eq_zero (a <<< (32 : Nat)) b h_disj).symm,
      BitVec.toNat_add_of_and_eq_zero h_disj, BitVec.toNat_shiftLeft]
  simp only [Nat.shiftLeft_eq]
  congr 1
  rw [show (2^64 : Nat) = 2^32 * 2^32 from by decide, Nat.mul_mod_mul_right]

/-- **V5.4.3 headline**: the Phase-1 adjusted remainder `un21` satisfies
    `un21 < vTop` unconditionally (no `uHi < 2^63` exclusion). Proof via the
    algebraic identity `un21.toNat = (uHi*2^32 + un1) % vTop`. The `Rhatdd <<< 32`
    truncation is harmless: it shifts the BitVec result by a multiple of 2^64,
    which cancels in the final modular calculation. -/
theorem divKTrialCallV5Un21_lt_vTop
    (uHi uLo vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63)
    (huHi_lt_vTop : uHi.toNat < vTop.toNat) :
    (divKTrialCallV5Un21 uHi uLo vTop).toNat < vTop.toNat := by
  rw [divKTrialCallV5Un21_unfold]
  dsimp only []
  -- Name the irreducible pieces.
  set Q := divKTrialCallV5Q1dd uHi uLo vTop
  set R := divKTrialCallV5Rhatdd uHi uLo vTop
  set dL := divKTrialCallV5DLo vTop with hdL
  set U1 := divKTrialCallV5Un1 uLo
  -- Gather key lemmas.
  have h_Q_eq : Q.toNat = (uHi.toNat * 2^32 + U1.toNat) / vTop.toNat :=
    divKTrialCallV5Q1dd_eq_q_true_1 uHi uLo vTop hvTop_ge huHi_lt_vTop
  have h_post : Q.toNat * (divKTrialCallV5DHi vTop).toNat + R.toNat = uHi.toNat :=
    divKTrialCallV5Q1dd_rhatdd_post uHi uLo vTop hvTop_ge
  have h_dL_bound : Q.toNat * dL.toNat ≤ R.toNat * 2^32 + U1.toNat :=
    divKTrialCallV5_phase1b_dLo_bound uHi uLo vTop hvTop_ge huHi_lt_vTop
  have h_QdL_nw : (Q * dL).toNat = Q.toNat * dL.toNat :=
    divKTrialCallV5Q1dd_dLo_no_wrap uHi uLo vTop
  have h_vTop_eq : vTop.toNat = (divKTrialCallV5DHi vTop).toNat * 2^32 + dL.toNat := by
    rw [hdL]; unfold divKTrialCallV5DHi divKTrialCallV5DLo
    exact div128Quot_vTop_decomp vTop
  have h_U1_lt : U1.toNat < 2^32 := divKTrialCallV5Un1_lt_pow32 uLo
  have h_dL_lt : dL.toNat < 2^32 := divKTrialCallV5DLo_lt_pow32 vTop
  -- Q < 2^32.
  have h_Q_lt : Q.toNat < 2^32 := by
    have h_le := divKTrialCallV5Q1dd_le_q_true_1 uHi uLo vTop hvTop_ge huHi_lt_vTop
    have h_N_lt : uHi.toNat * 2^32 + U1.toNat < vTop.toNat * 2^32 := by nlinarith
    have h_qt_lt : (uHi.toNat * 2^32 + U1.toNat) / vTop.toNat < 2^32 :=
      (Nat.div_lt_iff_lt_mul (by omega)).mpr (by linarith)
    omega
  have hvTop_pos : 0 < vTop.toNat := by omega
  -- Algebraic identity: R*2^32 + U1 = Q*dL + N%vTop.
  have h_alg : R.toNat * 2^32 + U1.toNat =
      Q.toNat * dL.toNat + (uHi.toNat * 2^32 + U1.toNat) % vTop.toNat := by
    -- N = vTop * Q + rem (division algorithm), vTop * Q = Q * vTop
    have hd := Nat.div_add_mod (uHi.toNat * 2^32 + U1.toNat) vTop.toNat
    -- hd : vTop * (N/vTop) + N%vTop = N
    -- Expand N as Q*dH*2^32 + R*2^32 + U1 and Q*vTop as Q*dH*2^32 + Q*dL.
    have hUH : uHi.toNat * 2^32 =
        Q.toNat * (divKTrialCallV5DHi vTop).toNat * 2^32 + R.toNat * 2^32 := by
      calc uHi.toNat * 2^32
          = (Q.toNat * (divKTrialCallV5DHi vTop).toNat + R.toNat) * 2^32 := by
            congr 1; linarith [h_post]
        _ = Q.toNat * (divKTrialCallV5DHi vTop).toNat * 2^32 + R.toNat * 2^32 := by ring
    have hQVT : vTop.toNat * ((uHi.toNat * 2^32 + U1.toNat) / vTop.toNat) =
        Q.toNat * (divKTrialCallV5DHi vTop).toNat * 2^32 + Q.toNat * dL.toNat := by
      rw [← h_Q_eq, h_vTop_eq]; ring
    linarith
  -- Combine formula: (R<<<32 ||| U1).toNat = (R%2^32)*2^32 + U1.
  have h_comb : ((R <<< (32 : BitVec 6).toNat) ||| U1).toNat =
      (R.toNat % 2^32) * 2^32 + U1.toNat := by
    have h32 : (32 : BitVec 6).toNat = 32 := by decide
    rw [h32]; exact halfword_combine_truncated R U1 h_U1_lt
  -- un21.toNat = ((R%2^32)*2^32 + U1 + 2^64 - Q*dL) % 2^64.
  have h_un21 : ((R <<< (32 : BitVec 6).toNat ||| U1) - Q * dL).toNat =
      ((R.toNat % 2^32) * 2^32 + U1.toNat + 2^64 - Q.toNat * dL.toNat) % 2^64 := by
    rw [BitVec.toNat_sub, h_comb, h_QdL_nw]; congr 1; omega
  rw [h_un21]
  -- Atom abbreviations for omega.
  set A := (R.toNat % 2^32) * 2^32 + U1.toNat with hA
  set B := Q.toNat * dL.toNat with hB
  set rem := (uHi.toNat * 2^32 + U1.toNat) % vTop.toNat with hrem_def
  have hrem_lt : rem < vTop.toNat := Nat.mod_lt _ hvTop_pos
  -- A + k*2^64 = B + rem  (k = R/2^32, from Nat_mul_pow32_split + h_alg).
  have h_decomp : A + (R.toNat / 2^32) * 2^64 = B + rem := by
    have hkey : R.toNat * 2^32 = (R.toNat / 2^32) * 2^64 + (R.toNat % 2^32) * 2^32 :=
      Nat_mul_pow32_split
    linarith [hA, hB, hrem_def, h_alg]
  -- Bounds.
  have h_A_lt : A < 2^64 := by
    have hmod := Nat.mod_lt R.toNat (show 0 < 2^32 from by norm_num)
    nlinarith [hA, h_U1_lt, hmod]
  have h_B_lt : B < 2^64 := by nlinarith [hB, h_Q_lt, h_dL_lt]
  have hrem_lt64 : rem < 2^64 := lt_trans hrem_lt (by have := vTop.isLt; omega)
  -- k ≤ 1.
  have h_k_le_1 : R.toNat / 2^32 ≤ 1 := by omega
  -- Case split k = 0 / k = 1, both giving rem % 2^64 = rem.
  rcases Nat.eq_zero_or_pos (R.toNat / 2^32) with hk0 | hk1_pos
  · have hkB : A + 2^64 - B = rem + 2^64 := by omega
    rw [hkB, Nat.add_mod_right, Nat.mod_eq_of_lt hrem_lt64]
    exact hrem_lt
  · have hk1 : R.toNat / 2^32 = 1 := Nat.le_antisymm h_k_le_1 hk1_pos
    have hkB : A + 2^64 - B = rem := by omega
    rw [hkB, Nat.mod_eq_of_lt hrem_lt64]
    exact hrem_lt

end EvmAsm.Evm64
