/-
  EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV5.Q1dNoFire

  When the V5 Phase-1b 1st correction does NOT fire, the post-1st-correction
  values `algorithmQ1dV5` / `algorithmRhatdV5` coincide with the
  Phase-1a-corrected values `algorithmQ1cV5` / `algorithmRhatcV5`.

  Mirror of v4's `algorithmQ1dV4_eq_q1c_of_phase1b_no_fire`
  (`Phase1bBound.lean:89`), but adapted to V5's stricter guard
  (`rhatc >>> 32 = 0 ∧ BLTU` vs v4's bare BLTU).

  Bead `evm-asm-wbc4i.4.6.8` (V5.4.0.9). Prerequisite for V5.4.1.
-/

import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV5.Phase1bNoFireBound

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- When Phase-1b 1st correction doesn't fire, `Q1d = Q1c`. -/
theorem algorithmQ1dV5_eq_q1c_of_phase1b_no_fire
    (uHi uLo vTop : Word)
    (h_no_fire : ¬ algorithmPhase1bFireV5 uHi uLo vTop) :
    algorithmQ1dV5 uHi uLo vTop = algorithmQ1cV5 uHi vTop := by
  rw [algorithmQ1dV5_unfold]
  dsimp only
  -- The let-bindings flatten; just need to show the if-condition is false.
  -- Direct case-split: show the fire condition is false.
  have h_fire_false :
      (decide (algorithmRhatcV5 uHi vTop >>> (32 : BitVec 6).toNat = 0) &&
        BitVec.ult
          ((algorithmRhatcV5 uHi vTop <<< (32 : BitVec 6).toNat) |||
            divKTrialCallV5Un1 uLo)
          (algorithmQ1cV5 uHi vTop * divKTrialCallV5DLo vTop)) ≠ true := by
    intro h_true
    rw [Bool.and_eq_true, decide_eq_true_eq] at h_true
    obtain ⟨h_hi, h_ult⟩ := h_true
    apply h_no_fire
    delta algorithmPhase1bFireV5 algorithmRhatUn1cV5
    exact ⟨h_hi, h_ult⟩
  simp only [h_fire_false, Bool.false_eq_true, if_false]

/-- When Phase-1b 1st correction doesn't fire, `Rhatd = Rhatc`. -/
theorem algorithmRhatdV5_eq_rhatc_of_phase1b_no_fire
    (uHi uLo vTop : Word)
    (h_no_fire : ¬ algorithmPhase1bFireV5 uHi uLo vTop) :
    algorithmRhatdV5 uHi uLo vTop = algorithmRhatcV5 uHi vTop := by
  rw [algorithmRhatdV5_unfold]
  dsimp only
  -- Direct case-split: show the fire condition is false.
  have h_fire_false :
      (decide (algorithmRhatcV5 uHi vTop >>> (32 : BitVec 6).toNat = 0) &&
        BitVec.ult
          ((algorithmRhatcV5 uHi vTop <<< (32 : BitVec 6).toNat) |||
            divKTrialCallV5Un1 uLo)
          (algorithmQ1cV5 uHi vTop * divKTrialCallV5DLo vTop)) ≠ true := by
    intro h_true
    rw [Bool.and_eq_true, decide_eq_true_eq] at h_true
    obtain ⟨h_hi, h_ult⟩ := h_true
    apply h_no_fire
    delta algorithmPhase1bFireV5 algorithmRhatUn1cV5
    exact ⟨h_hi, h_ult⟩
  simp only [h_fire_false, Bool.false_eq_true, if_false]

end EvmAsm.Evm64
