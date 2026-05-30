/-
  EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV5.Q0ddBound

  **V5.4.4**: `Q0dd.toNat ≤ q_true_0 + 1` unconditionally under V5.

  Two-case proof on hi2 = q0 >>> 32:
  - hi2 = 0 (Q0c = q0, Rhat2c = un21 % dHi < 2^32): case-split on
    Phase-2b fire guard. Fire gives Q0d = Q0c − 1 ≤ q_true_0 + 1 (Knuth-B:
    Q0c ≤ q_true_0 + 2). No-fire: dLo bound + Euclidean → Q0c ≤ q_true_0.
  - hi2 ≠ 0 (Q0c = cap = 2^32 − 1): Knuth-B + q0 ≥ 2^32 → q_true_0 ≥ 2^32 − 2,
    so cap ≤ q_true_0 + 1; Q0dd ≤ Q0c = cap ≤ q_true_0 + 1.

  Bead evm-asm-wbc4i.4.4 (V5.4.4).
-/

import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV5.Un21Bound
import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV4.Phase2bFireBound
import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV4.Phase2bNoFireBound

namespace EvmAsm.Evm64

open EvmAsm.Rv64 EvmWord

theorem divKTrialCallV5Q0dd_le_q_true_0_plus_one
    (uHi uLo vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63)
    (huHi_lt_vTop : uHi.toNat < vTop.toNat) :
    (divKTrialCallV5Q0dd uHi uLo vTop).toNat ≤
      ((divKTrialCallV5Un21 uHi uLo vTop).toNat * 2^32 +
          (divKTrialCallV5Un0 uLo).toNat) /
        vTop.toNat + 1 := by
  have h_un21_lt : (divKTrialCallV5Un21 uHi uLo vTop).toNat < vTop.toNat :=
    divKTrialCallV5Un21_lt_vTop uHi uLo vTop hvTop_ge huHi_lt_vTop
  have h_dHi_ge : (divKTrialCallV5DHi vTop).toNat ≥ 2^31 := by
    unfold divKTrialCallV5DHi
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]; omega
  have h_dHi_lt : (divKTrialCallV5DHi vTop).toNat < 2^32 := divKTrialCallV5DHi_lt_pow32 vTop
  have h_dHi_pos : 0 < (divKTrialCallV5DHi vTop).toNat := by omega
  have h_dLo_lt : (divKTrialCallV5DLo vTop).toNat < 2^32 := divKTrialCallV5DLo_lt_pow32 vTop
  have h_un0_lt : (divKTrialCallV5Un0 uLo).toNat < 2^32 := divKTrialCallV5Un0_lt_pow32 uLo
  have h_vTop_eq : vTop.toNat = (divKTrialCallV5DHi vTop).toNat * 2^32 +
      (divKTrialCallV5DLo vTop).toNat := by
    unfold divKTrialCallV5DHi divKTrialCallV5DLo; exact div128Quot_vTop_decomp vTop
  -- Monotonicity
  have h_q0dd_le_q0d : (divKTrialCallV5Q0dd uHi uLo vTop).toNat ≤
      (divKTrialCallV5Q0d uHi uLo vTop).toNat := by
    unfold divKTrialCallV5Q0dd; exact div128Quot_phase2b_q0'_le_self _ _ _ _
  have h_q0d_le_q0c : (divKTrialCallV5Q0d uHi uLo vTop).toNat ≤
      (divKTrialCallV5Q0c uHi uLo vTop).toNat := by
    unfold divKTrialCallV5Q0d; exact div128Quot_phase2b_q0'_le_self _ _ _ _
  -- Q0d definitional form
  have h_q0d_def : divKTrialCallV5Q0d uHi uLo vTop =
      div128Quot_phase2b_q0' (divKTrialCallV5Q0c uHi uLo vTop)
        (divKTrialCallV5Rhat2c uHi uLo vTop) (divKTrialCallV5DLo vTop)
        (divKTrialCallV5Un0 uLo) := by delta divKTrialCallV5Q0d; rfl
  -- Q0c < 2^32, no-wrap, Euclidean
  have h_q0c_lt : (divKTrialCallV5Q0c uHi uLo vTop).toNat < 2^32 := by
    rw [divKTrialCallV5Q0c_eq_algorithm]; exact algorithmQ0cV5_lt_pow32 uHi uLo vTop
  have h_q0c_nw : (divKTrialCallV5Q0c uHi uLo vTop * divKTrialCallV5DLo vTop).toNat =
      (divKTrialCallV5Q0c uHi uLo vTop).toNat * (divKTrialCallV5DLo vTop).toNat :=
    divKTrialCallV5Q0c_dLo_no_wrap uHi uLo vTop
  have h_eucl : (divKTrialCallV5Q0c uHi uLo vTop).toNat * (divKTrialCallV5DHi vTop).toNat +
      (divKTrialCallV5Rhat2c uHi uLo vTop).toNat =
      (divKTrialCallV5Un21 uHi uLo vTop).toNat := by
    rw [divKTrialCallV5Q0c_eq_algorithm, divKTrialCallV5Rhat2c_eq_algorithm]
    exact algorithmQ0cV5_rhat2c_post uHi uLo vTop hvTop_ge
  -- q0 and hi2 setup
  set un21 := divKTrialCallV5Un21 uHi uLo vTop
  set q0 : Word := rv64_divu un21 (divKTrialCallV5DHi vTop)
  have h_q0_toNat : q0.toNat = un21.toNat / (divKTrialCallV5DHi vTop).toNat := by
    unfold q0 rv64_divu
    have hne : ¬ (divKTrialCallV5DHi vTop == 0#64) := by
      simp only [beq_iff_eq]; intro h
      have : (divKTrialCallV5DHi vTop).toNat = 0 := by rw [h]; rfl
      omega
    rw [if_neg hne, BitVec.toNat_udiv]
  -- Helper: Knuth-B applied to un21 / vTop
  have h_knuthB : q0.toNat ≤
      (un21.toNat * 2^32 + (divKTrialCallV5Un0 uLo).toNat) / vTop.toNat + 2 := by
    rw [h_q0_toNat, h_vTop_eq]
    exact EvmWord.trial_quotient_le un21.toNat (divKTrialCallV5Un0 uLo).toNat
      (divKTrialCallV5DHi vTop).toNat (divKTrialCallV5DLo vTop).toNat
      h_dHi_lt h_dLo_lt h_un0_lt (by rw [← h_vTop_eq]; exact h_un21_lt) h_dHi_ge
  by_cases h_hi2 : q0 >>> (32 : BitVec 6).toNat = (0 : Word)
  · -- hi2 = 0: Q0c = q0, Rhat2c = un21 % dHi < dHi < 2^32
    have h_q0c_eq : (divKTrialCallV5Q0c uHi uLo vTop).toNat = q0.toNat := by
      rw [divKTrialCallV5Q0c_eq_algorithm, algorithmQ0cV5_unfold]; dsimp only
      rw [show rv64_divu un21 (divKTrialCallV5DHi vTop) = q0 from rfl, if_pos h_hi2]
    -- Rhat2c = un21 % dHi (via Euclidean - Q0c * dHi)
    have h_rhat2c_lt : (divKTrialCallV5Rhat2c uHi uLo vTop).toNat < 2^32 := by
      have h_eq : (divKTrialCallV5Rhat2c uHi uLo vTop).toNat =
          un21.toNat % (divKTrialCallV5DHi vTop).toNat := by
        have hEucl := h_eucl
        rw [h_q0c_eq, h_q0_toNat] at hEucl
        have hDivMod := Nat.div_add_mod un21.toNat (divKTrialCallV5DHi vTop).toNat
        have hComm := Nat.mul_comm (un21.toNat / (divKTrialCallV5DHi vTop).toNat)
          (divKTrialCallV5DHi vTop).toNat
        omega
      rw [h_eq]
      exact lt_of_lt_of_le (Nat.mod_lt _ h_dHi_pos) (le_of_lt h_dHi_lt)
    -- Q0c Knuth-B
    have h_q0c_le_plus2 : (divKTrialCallV5Q0c uHi uLo vTop).toNat ≤
        (un21.toNat * 2^32 + (divKTrialCallV5Un0 uLo).toNat) / vTop.toNat + 2 := by
      rw [h_q0c_eq]; exact h_knuthB
    -- Phase-2b fire/no-fire
    by_cases h_guard :
        divKTrialCallV5Rhat2c uHi uLo vTop >>> (32 : BitVec 6).toNat = (0 : Word) ∧
        BitVec.ult ((divKTrialCallV5Rhat2c uHi uLo vTop <<< (32 : BitVec 6).toNat) |||
              divKTrialCallV5Un0 uLo)
          (divKTrialCallV5Q0c uHi uLo vTop * divKTrialCallV5DLo vTop)
    · -- Fire: Q0d = Q0c - 1 ≤ q_true_0 + 1
      have h_q0c_pos : 1 ≤ (divKTrialCallV5Q0c uHi uLo vTop).toNat := by
        rcases Nat.eq_zero_or_pos (divKTrialCallV5Q0c uHi uLo vTop).toNat with h | h
        · exfalso
          have hq0 : divKTrialCallV5Q0c uHi uLo vTop = 0 := BitVec.eq_of_toNat_eq h
          simp only [hq0] at h_guard
          simp [BitVec.ult] at h_guard
        · exact h
      have h_dec : divKTrialCallV5Q0d uHi uLo vTop =
          divKTrialCallV5Q0c uHi uLo vTop + signExtend12 4095 := by
        rw [h_q0d_def]
        exact div128Quot_phase2b_q0'_eq_q_dec_of_fire _ _ _ _ h_guard.1 h_guard.2
      have h_q0d_nat : (divKTrialCallV5Q0d uHi uLo vTop).toNat =
          (divKTrialCallV5Q0c uHi uLo vTop).toNat - 1 := by
        rw [h_dec, BitVec.toNat_add,
            show (signExtend12 4095 : Word).toNat = 2^64 - 1 from by decide]; omega
      omega
    · -- No-fire: Q0d = Q0c, dLo bound → Q0c ≤ q_true_0
      obtain ⟨h_q0d_eq, h_dlo⟩ :=
        div128Quot_phase2b_q0'_dLo_bound_no_fire
          (divKTrialCallV5Q0c uHi uLo vTop) (divKTrialCallV5Rhat2c uHi uLo vTop)
          (divKTrialCallV5DLo vTop) (divKTrialCallV5Un0 uLo)
          (by omega) h_dLo_lt h_un0_lt h_q0c_nw h_guard
      have h_q0c_vTop : (divKTrialCallV5Q0c uHi uLo vTop).toNat * vTop.toNat ≤
          un21.toNat * 2^32 + (divKTrialCallV5Un0 uLo).toNat := by
        calc (divKTrialCallV5Q0c uHi uLo vTop).toNat * vTop.toNat
            = (divKTrialCallV5Q0c uHi uLo vTop).toNat * (divKTrialCallV5DHi vTop).toNat * 2^32 +
              (divKTrialCallV5Q0c uHi uLo vTop).toNat * (divKTrialCallV5DLo vTop).toNat := by
              rw [h_vTop_eq]; ring
          _ ≤ (divKTrialCallV5Q0c uHi uLo vTop).toNat * (divKTrialCallV5DHi vTop).toNat * 2^32 +
              ((divKTrialCallV5Rhat2c uHi uLo vTop).toNat * 2^32 +
                (divKTrialCallV5Un0 uLo).toNat) := by omega
          _ = ((divKTrialCallV5Q0c uHi uLo vTop).toNat * (divKTrialCallV5DHi vTop).toNat +
              (divKTrialCallV5Rhat2c uHi uLo vTop).toNat) * 2^32 +
              (divKTrialCallV5Un0 uLo).toNat := by ring
          _ = un21.toNat * 2^32 + (divKTrialCallV5Un0 uLo).toNat := by rw [h_eucl]
      have h_q0c_le : (divKTrialCallV5Q0c uHi uLo vTop).toNat ≤
          (un21.toNat * 2^32 + (divKTrialCallV5Un0 uLo).toNat) / vTop.toNat :=
        (Nat.le_div_iff_mul_le (by omega)).mpr h_q0c_vTop
      have h_q0d_nat : (divKTrialCallV5Q0d uHi uLo vTop).toNat =
          (divKTrialCallV5Q0c uHi uLo vTop).toNat := by
        congr 1; rw [h_q0d_def]; exact h_q0d_eq
      linarith [h_q0dd_le_q0d, h_q0c_le,
                show (divKTrialCallV5Q0d uHi uLo vTop).toNat =
                     (divKTrialCallV5Q0c uHi uLo vTop).toNat from h_q0d_nat]
  · -- hi2 ≠ 0: Q0c = cap = 2^32 - 1, q0 ≥ 2^32 → q_true_0 ≥ 2^32 - 2
    have h_q0_ge : q0.toNat ≥ 2^32 := by
      by_contra h; push Not at h
      apply h_hi2; apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow,
          Nat.div_eq_of_lt h]; rfl
    have h_q0c_cap : (divKTrialCallV5Q0c uHi uLo vTop).toNat = 2^32 - 1 := by
      rw [divKTrialCallV5Q0c_eq_algorithm, algorithmQ0cV5_unfold]; dsimp only
      rw [show rv64_divu un21 (divKTrialCallV5DHi vTop) = q0 from rfl, if_neg h_hi2]; decide
    have h_q0c_le : (divKTrialCallV5Q0c uHi uLo vTop).toNat ≤
        (un21.toNat * 2^32 + (divKTrialCallV5Un0 uLo).toNat) / vTop.toNat + 1 := by
      rw [h_q0c_cap]; omega
    linarith [h_q0dd_le_q0d, h_q0d_le_q0c, h_q0c_le]

/-- **First-stage Phase-2b bound**: `Q0d ≤ q_true_0 + 1`.

    `divKTrialCallV5Q0dd_le_q_true_0_plus_one` above is the `Q0dd ≤ Q0d`
    corollary of this. `Q0d` (the once-corrected half-quotient) is the input to
    the *second*-correction exactness argument (`Q0dd ≤ q_true_0`, bead
    `wbc4i.8.2.2.7`): when the second Phase-2b guard fires, `Q0dd = Q0d - 1 ≤
    q_true_0`; when it does not, the dLo-check pins `Q0d ≤ q_true_0`. -/
theorem divKTrialCallV5Q0d_le_q_true_0_plus_one
    (uHi uLo vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63)
    (huHi_lt_vTop : uHi.toNat < vTop.toNat) :
    (divKTrialCallV5Q0d uHi uLo vTop).toNat ≤
      ((divKTrialCallV5Un21 uHi uLo vTop).toNat * 2^32 +
          (divKTrialCallV5Un0 uLo).toNat) /
        vTop.toNat + 1 := by
  have h_un21_lt : (divKTrialCallV5Un21 uHi uLo vTop).toNat < vTop.toNat :=
    divKTrialCallV5Un21_lt_vTop uHi uLo vTop hvTop_ge huHi_lt_vTop
  have h_dHi_ge : (divKTrialCallV5DHi vTop).toNat ≥ 2^31 := by
    unfold divKTrialCallV5DHi
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]; omega
  have h_dHi_lt : (divKTrialCallV5DHi vTop).toNat < 2^32 := divKTrialCallV5DHi_lt_pow32 vTop
  have h_dHi_pos : 0 < (divKTrialCallV5DHi vTop).toNat := by omega
  have h_dLo_lt : (divKTrialCallV5DLo vTop).toNat < 2^32 := divKTrialCallV5DLo_lt_pow32 vTop
  have h_un0_lt : (divKTrialCallV5Un0 uLo).toNat < 2^32 := divKTrialCallV5Un0_lt_pow32 uLo
  have h_vTop_eq : vTop.toNat = (divKTrialCallV5DHi vTop).toNat * 2^32 +
      (divKTrialCallV5DLo vTop).toNat := by
    unfold divKTrialCallV5DHi divKTrialCallV5DLo; exact div128Quot_vTop_decomp vTop
  have h_q0d_le_q0c : (divKTrialCallV5Q0d uHi uLo vTop).toNat ≤
      (divKTrialCallV5Q0c uHi uLo vTop).toNat := by
    unfold divKTrialCallV5Q0d; exact div128Quot_phase2b_q0'_le_self _ _ _ _
  have h_q0d_def : divKTrialCallV5Q0d uHi uLo vTop =
      div128Quot_phase2b_q0' (divKTrialCallV5Q0c uHi uLo vTop)
        (divKTrialCallV5Rhat2c uHi uLo vTop) (divKTrialCallV5DLo vTop)
        (divKTrialCallV5Un0 uLo) := by delta divKTrialCallV5Q0d; rfl
  have h_q0c_lt : (divKTrialCallV5Q0c uHi uLo vTop).toNat < 2^32 := by
    rw [divKTrialCallV5Q0c_eq_algorithm]; exact algorithmQ0cV5_lt_pow32 uHi uLo vTop
  have h_q0c_nw : (divKTrialCallV5Q0c uHi uLo vTop * divKTrialCallV5DLo vTop).toNat =
      (divKTrialCallV5Q0c uHi uLo vTop).toNat * (divKTrialCallV5DLo vTop).toNat :=
    divKTrialCallV5Q0c_dLo_no_wrap uHi uLo vTop
  have h_eucl : (divKTrialCallV5Q0c uHi uLo vTop).toNat * (divKTrialCallV5DHi vTop).toNat +
      (divKTrialCallV5Rhat2c uHi uLo vTop).toNat =
      (divKTrialCallV5Un21 uHi uLo vTop).toNat := by
    rw [divKTrialCallV5Q0c_eq_algorithm, divKTrialCallV5Rhat2c_eq_algorithm]
    exact algorithmQ0cV5_rhat2c_post uHi uLo vTop hvTop_ge
  set un21 := divKTrialCallV5Un21 uHi uLo vTop
  set q0 : Word := rv64_divu un21 (divKTrialCallV5DHi vTop)
  have h_q0_toNat : q0.toNat = un21.toNat / (divKTrialCallV5DHi vTop).toNat := by
    unfold q0 rv64_divu
    have hne : ¬ (divKTrialCallV5DHi vTop == 0#64) := by
      simp only [beq_iff_eq]; intro h
      have : (divKTrialCallV5DHi vTop).toNat = 0 := by rw [h]; rfl
      omega
    rw [if_neg hne, BitVec.toNat_udiv]
  have h_knuthB : q0.toNat ≤
      (un21.toNat * 2^32 + (divKTrialCallV5Un0 uLo).toNat) / vTop.toNat + 2 := by
    rw [h_q0_toNat, h_vTop_eq]
    exact EvmWord.trial_quotient_le un21.toNat (divKTrialCallV5Un0 uLo).toNat
      (divKTrialCallV5DHi vTop).toNat (divKTrialCallV5DLo vTop).toNat
      h_dHi_lt h_dLo_lt h_un0_lt (by rw [← h_vTop_eq]; exact h_un21_lt) h_dHi_ge
  by_cases h_hi2 : q0 >>> (32 : BitVec 6).toNat = (0 : Word)
  · have h_q0c_eq : (divKTrialCallV5Q0c uHi uLo vTop).toNat = q0.toNat := by
      rw [divKTrialCallV5Q0c_eq_algorithm, algorithmQ0cV5_unfold]; dsimp only
      rw [show rv64_divu un21 (divKTrialCallV5DHi vTop) = q0 from rfl, if_pos h_hi2]
    have h_rhat2c_lt : (divKTrialCallV5Rhat2c uHi uLo vTop).toNat < 2^32 := by
      have h_eq : (divKTrialCallV5Rhat2c uHi uLo vTop).toNat =
          un21.toNat % (divKTrialCallV5DHi vTop).toNat := by
        have hEucl := h_eucl
        rw [h_q0c_eq, h_q0_toNat] at hEucl
        have hDivMod := Nat.div_add_mod un21.toNat (divKTrialCallV5DHi vTop).toNat
        have hComm := Nat.mul_comm (un21.toNat / (divKTrialCallV5DHi vTop).toNat)
          (divKTrialCallV5DHi vTop).toNat
        omega
      rw [h_eq]
      exact lt_of_lt_of_le (Nat.mod_lt _ h_dHi_pos) (le_of_lt h_dHi_lt)
    have h_q0c_le_plus2 : (divKTrialCallV5Q0c uHi uLo vTop).toNat ≤
        (un21.toNat * 2^32 + (divKTrialCallV5Un0 uLo).toNat) / vTop.toNat + 2 := by
      rw [h_q0c_eq]; exact h_knuthB
    by_cases h_guard :
        divKTrialCallV5Rhat2c uHi uLo vTop >>> (32 : BitVec 6).toNat = (0 : Word) ∧
        BitVec.ult ((divKTrialCallV5Rhat2c uHi uLo vTop <<< (32 : BitVec 6).toNat) |||
              divKTrialCallV5Un0 uLo)
          (divKTrialCallV5Q0c uHi uLo vTop * divKTrialCallV5DLo vTop)
    · have h_q0c_pos : 1 ≤ (divKTrialCallV5Q0c uHi uLo vTop).toNat := by
        rcases Nat.eq_zero_or_pos (divKTrialCallV5Q0c uHi uLo vTop).toNat with h | h
        · exfalso
          have hq0 : divKTrialCallV5Q0c uHi uLo vTop = 0 := BitVec.eq_of_toNat_eq h
          simp only [hq0] at h_guard
          simp [BitVec.ult] at h_guard
        · exact h
      have h_dec : divKTrialCallV5Q0d uHi uLo vTop =
          divKTrialCallV5Q0c uHi uLo vTop + signExtend12 4095 := by
        rw [h_q0d_def]
        exact div128Quot_phase2b_q0'_eq_q_dec_of_fire _ _ _ _ h_guard.1 h_guard.2
      have h_q0d_nat : (divKTrialCallV5Q0d uHi uLo vTop).toNat =
          (divKTrialCallV5Q0c uHi uLo vTop).toNat - 1 := by
        rw [h_dec, BitVec.toNat_add,
            show (signExtend12 4095 : Word).toNat = 2^64 - 1 from by decide]; omega
      omega
    · obtain ⟨h_q0d_eq, h_dlo⟩ :=
        div128Quot_phase2b_q0'_dLo_bound_no_fire
          (divKTrialCallV5Q0c uHi uLo vTop) (divKTrialCallV5Rhat2c uHi uLo vTop)
          (divKTrialCallV5DLo vTop) (divKTrialCallV5Un0 uLo)
          (by omega) h_dLo_lt h_un0_lt h_q0c_nw h_guard
      have h_q0c_vTop : (divKTrialCallV5Q0c uHi uLo vTop).toNat * vTop.toNat ≤
          un21.toNat * 2^32 + (divKTrialCallV5Un0 uLo).toNat := by
        calc (divKTrialCallV5Q0c uHi uLo vTop).toNat * vTop.toNat
            = (divKTrialCallV5Q0c uHi uLo vTop).toNat * (divKTrialCallV5DHi vTop).toNat * 2^32 +
              (divKTrialCallV5Q0c uHi uLo vTop).toNat * (divKTrialCallV5DLo vTop).toNat := by
              rw [h_vTop_eq]; ring
          _ ≤ (divKTrialCallV5Q0c uHi uLo vTop).toNat * (divKTrialCallV5DHi vTop).toNat * 2^32 +
              ((divKTrialCallV5Rhat2c uHi uLo vTop).toNat * 2^32 +
                (divKTrialCallV5Un0 uLo).toNat) := by omega
          _ = ((divKTrialCallV5Q0c uHi uLo vTop).toNat * (divKTrialCallV5DHi vTop).toNat +
              (divKTrialCallV5Rhat2c uHi uLo vTop).toNat) * 2^32 +
              (divKTrialCallV5Un0 uLo).toNat := by ring
          _ = un21.toNat * 2^32 + (divKTrialCallV5Un0 uLo).toNat := by rw [h_eucl]
      have h_q0c_le : (divKTrialCallV5Q0c uHi uLo vTop).toNat ≤
          (un21.toNat * 2^32 + (divKTrialCallV5Un0 uLo).toNat) / vTop.toNat :=
        (Nat.le_div_iff_mul_le (by omega)).mpr h_q0c_vTop
      have h_q0d_nat : (divKTrialCallV5Q0d uHi uLo vTop).toNat =
          (divKTrialCallV5Q0c uHi uLo vTop).toNat := by
        congr 1; rw [h_q0d_def]; exact h_q0d_eq
      omega
  · have h_q0_ge : q0.toNat ≥ 2^32 := by
      by_contra h; push Not at h
      apply h_hi2; apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow,
          Nat.div_eq_of_lt h]; rfl
    have h_q0c_cap : (divKTrialCallV5Q0c uHi uLo vTop).toNat = 2^32 - 1 := by
      rw [divKTrialCallV5Q0c_eq_algorithm, algorithmQ0cV5_unfold]; dsimp only
      rw [show rv64_divu un21 (divKTrialCallV5DHi vTop) = q0 from rfl, if_neg h_hi2]; decide
    have h_q0c_le : (divKTrialCallV5Q0c uHi uLo vTop).toNat ≤
        (un21.toNat * 2^32 + (divKTrialCallV5Un0 uLo).toNat) / vTop.toNat + 1 := by
      rw [h_q0c_cap]; omega
    omega

end EvmAsm.Evm64
