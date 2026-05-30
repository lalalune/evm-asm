/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN2V5NoNopLoopDispatch

  The 8 dispatch helpers for the unified n=2 v5 loop: each derives a combo's
  `loopN2{Combo}SourceCondsV5` from the selected-carry bundle
  `loopN2SelectedCarryV5 b2 b1 b0 ...` plus the three path `bltu` facts.  Mirror
  of the v4 `loopN2{Combo}SourceConds_of_selectedCarryV4` helpers
  (FullPathN2V4NoNopLoopUnified), using the v5 trial accessors and the v5
  per-prefix aliases (note cmc/mcm/mmm reuse r1TMM/r1MTT/r1MMT).
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN2V5NoNopLoopDefs
import EvmAsm.Evm64.DivMod.Compose.FullPathN2V5NoNopComboCCC
import EvmAsm.Evm64.DivMod.Compose.FullPathN2V5NoNopComboCCM

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- ccc (TTT). -/
theorem loopN2CallCallCallSourceConds_of_selectedCarryV5
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 : Word)
    (hbltu_2 : BitVec.ult u2 v1)
    (hbltu_1 : BitVec.ult
      (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1 v1)
    (hbltu_0 : BitVec.ult
      (iterWithDoubleAddback
        (divKTrialCallV5QHat
          (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
          (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v1)
        v0 v1 v2 v3 u0Orig1
        (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1 v1)
    (hcarry : loopN2SelectedCarryV5 true true true
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0) :
    loopN2CallCallCallSourceCondsV5 v0 v1 v2 v3 u0 u1 u2 u3 uTop
      u0Orig1 u0Orig0 := by
  rw [loopN2SelectedCarryV5_unfold] at hcarry
  rw [loopN2CallCallCallSourceCondsV5_unfold]
  simp only [loopN2IterSelectedV5_true, r2CCCN2V5_eq, r1CCCN2V5_eq] at hcarry ⊢
  exact ⟨hbltu_2, hcarry.1, hbltu_1, hcarry.2.1, hbltu_0, hcarry.2.2⟩

/-- ccm (TTF). -/
theorem loopN2CallCallMaxSourceConds_of_selectedCarryV5
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 : Word)
    (hbltu_2 : BitVec.ult u2 v1)
    (hbltu_1 : BitVec.ult
      (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1 v1)
    (hbltu_0 : ¬BitVec.ult
      (iterWithDoubleAddback
        (divKTrialCallV5QHat
          (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
          (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v1)
        v0 v1 v2 v3 u0Orig1
        (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1 v1)
    (hcarry : loopN2SelectedCarryV5 true true false
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0) :
    loopN2CallCallMaxSourceCondsV5 v0 v1 v2 v3 u0 u1 u2 u3 uTop
      u0Orig1 u0Orig0 := by
  rw [loopN2SelectedCarryV5_unfold] at hcarry
  rw [loopN2CallCallMaxSourceCondsV5_unfold]
  simp only [loopN2IterSelectedV5_true, r2CCCN2V5_eq, r1CCCN2V5_eq] at hcarry ⊢
  exact ⟨hbltu_2, hcarry.1, hbltu_1, hcarry.2.1, hbltu_0, hcarry.2.2⟩

/-- cmc (TFT). -/
theorem loopN2CallMaxCallSourceConds_of_selectedCarryV5
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 : Word)
    (hbltu_2 : BitVec.ult u2 v1)
    (hbltu_1 : ¬BitVec.ult
      (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1 v1)
    (hbltu_0 : BitVec.ult
      (iterN2Max v0 v1 v2 v3 u0Orig1
        (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1 v1)
    (hcarry : loopN2SelectedCarryV5 true false true
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0) :
    loopN2CallMaxCallSourceCondsV5 v0 v1 v2 v3 u0 u1 u2 u3 uTop
      u0Orig1 u0Orig0 := by
  rw [loopN2SelectedCarryV5_unfold] at hcarry
  rw [loopN2CallMaxCallSourceCondsV5_unfold]
  simp only [loopN2IterSelectedV5_true, loopN2IterSelectedV5_false,
    r2CCCN2V5_eq, r1TMMN2V5_eq] at hcarry ⊢
  exact ⟨hbltu_2, hcarry.1, hbltu_1, hcarry.2.1, hbltu_0, hcarry.2.2⟩

/-- cmm (TFF). -/
theorem loopN2CallMaxMaxSourceConds_of_selectedCarryV5
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 : Word)
    (hbltu_2 : BitVec.ult u2 v1)
    (hbltu_1 : ¬BitVec.ult
      (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1 v1)
    (hbltu_0 : ¬BitVec.ult
      (iterN2Max v0 v1 v2 v3 u0Orig1
        (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1 v1)
    (hcarry : loopN2SelectedCarryV5 true false false
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0) :
    loopN2CallMaxMaxSourceCondsV5 v0 v1 v2 v3 u0 u1 u2 u3 uTop
      u0Orig1 u0Orig0 := by
  rw [loopN2SelectedCarryV5_unfold] at hcarry
  rw [loopN2CallMaxMaxSourceCondsV5_unfold]
  simp only [loopN2IterSelectedV5_true, loopN2IterSelectedV5_false,
    r2CCCN2V5_eq, r1TMMN2V5_eq] at hcarry ⊢
  exact ⟨hbltu_2, hcarry.1, hbltu_1, hcarry.2.1, hbltu_0, hcarry.2.2⟩

/-- mcc (FTT). -/
theorem loopN2MaxCallCallSourceConds_of_selectedCarryV5
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 : Word)
    (hbltu_2 : ¬BitVec.ult u2 v1)
    (hbltu_1 : BitVec.ult
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1 v1)
    (hbltu_0 : BitVec.ult
      (iterWithDoubleAddback
        (divKTrialCallV5QHat
          (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
          (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v1)
        v0 v1 v2 v3 u0Orig1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1 v1)
    (hcarry : loopN2SelectedCarryV5 false true true
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0) :
    loopN2MaxCallCallSourceCondsV5 v0 v1 v2 v3 u0 u1 u2 u3 uTop
      u0Orig1 u0Orig0 := by
  rw [loopN2SelectedCarryV5_unfold] at hcarry
  rw [loopN2MaxCallCallSourceCondsV5_unfold]
  simp only [loopN2IterSelectedV5_false, loopN2IterSelectedV5_true,
    r2MTTN2V5_eq, r1MTTN2V5_eq] at hcarry ⊢
  exact ⟨hbltu_2, hcarry.1, hbltu_1, hcarry.2.1, hbltu_0, hcarry.2.2⟩

/-- mcm (FTF). -/
theorem loopN2MaxCallMaxSourceConds_of_selectedCarryV5
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 : Word)
    (hbltu_2 : ¬BitVec.ult u2 v1)
    (hbltu_1 : BitVec.ult
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1 v1)
    (hbltu_0 : ¬BitVec.ult
      (iterWithDoubleAddback
        (divKTrialCallV5QHat
          (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
          (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v1)
        v0 v1 v2 v3 u0Orig1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1 v1)
    (hcarry : loopN2SelectedCarryV5 false true false
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0) :
    loopN2MaxCallMaxSourceCondsV5 v0 v1 v2 v3 u0 u1 u2 u3 uTop
      u0Orig1 u0Orig0 := by
  rw [loopN2SelectedCarryV5_unfold] at hcarry
  rw [loopN2MaxCallMaxSourceCondsV5_unfold]
  simp only [loopN2IterSelectedV5_false, loopN2IterSelectedV5_true,
    r2MTTN2V5_eq, r1MTTN2V5_eq] at hcarry ⊢
  exact ⟨hbltu_2, hcarry.1, hbltu_1, hcarry.2.1, hbltu_0, hcarry.2.2⟩

/-- mmc (FFT). -/
theorem loopN2MaxMaxCallSourceConds_of_selectedCarryV5
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 : Word)
    (hbltu_2 : ¬BitVec.ult u2 v1)
    (hbltu_1 : ¬BitVec.ult
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1 v1)
    (hbltu_0 : BitVec.ult
      (iterN2Max v0 v1 v2 v3 u0Orig1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1 v1)
    (hcarry : loopN2SelectedCarryV5 false false true
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0) :
    loopN2MaxMaxCallSourceCondsV5 v0 v1 v2 v3 u0 u1 u2 u3 uTop
      u0Orig1 u0Orig0 := by
  rw [loopN2SelectedCarryV5_unfold] at hcarry
  rw [loopN2MaxMaxCallSourceCondsV5_unfold]
  simp only [loopN2IterSelectedV5_false, r2MMTN2V5_eq, r1MMTN2V5_eq] at hcarry ⊢
  exact ⟨hbltu_2, hcarry.1, hbltu_1, hcarry.2.1, hbltu_0, hcarry.2.2⟩

/-- mmm (FFF). -/
theorem loopN2MaxMaxMaxSourceConds_of_selectedCarryV5
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 : Word)
    (hbltu_2 : ¬BitVec.ult u2 v1)
    (hbltu_1 : ¬BitVec.ult
      (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1 v1)
    (hbltu_0 : ¬BitVec.ult
      (iterN2Max v0 v1 v2 v3 u0Orig1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1 v1)
    (hcarry : loopN2SelectedCarryV5 false false false
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0) :
    loopN2MaxMaxMaxSourceCondsV5 v0 v1 v2 v3 u0 u1 u2 u3 uTop
      u0Orig1 u0Orig0 := by
  rw [loopN2SelectedCarryV5_unfold] at hcarry
  rw [loopN2MaxMaxMaxSourceCondsV5_unfold]
  simp only [loopN2IterSelectedV5_false, r2MMTN2V5_eq, r1MMTN2V5_eq] at hcarry ⊢
  exact ⟨hbltu_2, hcarry.1, hbltu_1, hcarry.2.1, hbltu_0, hcarry.2.2⟩

end EvmAsm.Evm64
