/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN2V5NoNopLoopUnified

  The unified n=2 v5/no-NOP loop source theorem (selected-carry), dispatching on
  `bltu_2 × bltu_1 × bltu_0` to the 8 combo theorems via the dispatch helpers.
  Mirror of `divK_loop_n2_unified_from_source_exact_loopIterScratch_v4_noNop_selectedCarry`
  (FullPathN2V4NoNopLoopSelected).  Worst-case bound 702 = 234·3 (all-call);
  lighter paths fit via `cpsTripleWithin_mono_nSteps`.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN2V5NoNopUnifiedPost

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Selected-carry unified n=2 v5 loop source theorem. -/
theorem divK_loop_n2_unified_from_source_exact_loopIterScratch_v5_noNop_selectedCarry
    (bltu_2 bltu_1 bltu_0 : Bool) (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu_2 : bltu_2 = BitVec.ult u2 v1)
    (hbltu_1 : bltu_1 =
      match bltu_2 with
      | false => BitVec.ult (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1 v1
      | true =>
        BitVec.ult (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
          v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1 v1)
    (hbltu_0 : bltu_0 =
      match bltu_2, bltu_1 with
      | false, false =>
        BitVec.ult (iterN2Max v0 v1 v2 v3 u0Orig1
          (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
          (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
          (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
          (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1 v1
      | false, true =>
        BitVec.ult (iterWithDoubleAddback
          (divKTrialCallV5QHat (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
            (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v1)
          v0 v1 v2 v3 u0Orig1
          (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
          (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
          (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
          (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1 v1
      | true, false =>
        BitVec.ult (iterN2Max v0 v1 v2 v3 u0Orig1
          (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
          (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
          (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
          (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1 v1
      | true, true =>
        BitVec.ult (iterWithDoubleAddback
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
    (hcarry : loopN2SelectedCarryV5 bltu_2 bltu_1 bltu_0
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0) :
    cpsTripleWithin 702 (base + loopBodyOff) (base + denormOff)
      (divCode_noNop_v5 base)
      (loopN2PreWithScratchV4NoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal))
      (loopN2UnifiedPostV5NoX1 bltu_2 bltu_1 bltu_0 sp base
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal)) := by
  cases bltu_2 <;> cases bltu_1 <;> cases bltu_0
  · -- FFF = MMM
    have hb2 : ¬BitVec.ult u2 v1 := by rw [show BitVec.ult u2 v1 = false from hbltu_2.symm]; decide
    have hb1 : ¬BitVec.ult (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1 v1 := by
      simp only at hbltu_1; rw [show BitVec.ult _ v1 = false from hbltu_1.symm]; decide
    have hb0 : ¬BitVec.ult (iterN2Max v0 v1 v2 v3 u0Orig1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1 v1 := by
      simp only at hbltu_0; rw [show BitVec.ult _ v1 = false from hbltu_0.symm]; decide
    have hconds := loopN2MaxMaxMaxSourceConds_of_selectedCarryV5
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 hb2 hb1 hb0 hcarry
    exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
      (fun _ hp => hp)
      (fun _ hp => by
        simp only [loopN2MaxMaxMaxSourceFinalPostNoX1V5_unfold, r2MMTN2V5_eq, r1MMTN2V5_eq] at hp
        unfold loopN2UnifiedPostV5NoX1
        simp only [r2MMTN2V5_eq, r1MMTN2V5_eq]
        xperm_hyp hp)
      (divK_loop_n2_max_max_max_from_source_exact_loopIterScratch_v5_noNop
        sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old raVal
        retMem dMem dloMem scratchUn0 scratchMem hconds)
  · -- FFT = MMC
    have hb2 : ¬BitVec.ult u2 v1 := by rw [show BitVec.ult u2 v1 = false from hbltu_2.symm]; decide
    have hb1 : ¬BitVec.ult (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1 v1 := by
      simp only at hbltu_1; rw [show BitVec.ult _ v1 = false from hbltu_1.symm]; decide
    have hb0 : BitVec.ult (iterN2Max v0 v1 v2 v3 u0Orig1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
        (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1 v1 := by
      simp only at hbltu_0; exact hbltu_0.symm
    have hconds := loopN2MaxMaxCallSourceConds_of_selectedCarryV5
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 hb2 hb1 hb0 hcarry
    exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
      (fun _ hp => hp)
      (fun _ hp => by
        simp only [loopN2MaxMaxCallSourceFinalPostNoX1V5_unfold, r2MMTN2V5_eq, r1MMTN2V5_eq] at hp
        unfold loopN2UnifiedPostV5NoX1
        simp only [r2MMTN2V5_eq, r1MMTN2V5_eq]
        xperm_hyp hp)
      (divK_loop_n2_max_max_call_from_source_exact_loopIterScratch_v5_noNop
        sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old raVal
        retMem dMem dloMem scratchUn0 scratchMem halign hconds)
  · -- FTF = MCM
    have hb2 : ¬BitVec.ult u2 v1 := by rw [show BitVec.ult u2 v1 = false from hbltu_2.symm]; decide
    have hb1 : BitVec.ult (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1 v1 := by
      simp only at hbltu_1; exact hbltu_1.symm
    have hb0 : ¬BitVec.ult
        (iterWithDoubleAddback
          (divKTrialCallV5QHat (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
            (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v1)
          v0 v1 v2 v3 u0Orig1
          (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
          (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
          (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
          (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1 v1 := by
      simp only at hbltu_0; rw [show BitVec.ult _ v1 = false from hbltu_0.symm]; decide
    have hconds := loopN2MaxCallMaxSourceConds_of_selectedCarryV5
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 hb2 hb1 hb0 hcarry
    exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
      (fun _ hp => hp)
      (fun _ hp => by
        simp only [loopN2MaxCallMaxSourceFinalPostNoX1V5_unfold, r2MTTN2V5_eq, r1MTTN2V5_eq] at hp
        unfold loopN2UnifiedPostV5NoX1
        simp only [r2MTTN2V5_eq, r1MTTN2V5_eq]
        xperm_hyp hp)
      (divK_loop_n2_max_call_max_from_source_exact_loopIterScratch_v5_noNop
        sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old raVal
        retMem dMem dloMem scratchUn0 scratchMem halign hconds)
  · -- FTT = MCC
    have hb2 : ¬BitVec.ult u2 v1 := by rw [show BitVec.ult u2 v1 = false from hbltu_2.symm]; decide
    have hb1 : BitVec.ult (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1 v1 := by
      simp only at hbltu_1; exact hbltu_1.symm
    have hb0 : BitVec.ult
        (iterWithDoubleAddback
          (divKTrialCallV5QHat (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
            (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1 v1)
          v0 v1 v2 v3 u0Orig1
          (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
          (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
          (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
          (iterN2Max v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1 v1 := by
      simp only at hbltu_0; exact hbltu_0.symm
    have hconds := loopN2MaxCallCallSourceConds_of_selectedCarryV5
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 hb2 hb1 hb0 hcarry
    exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
      (fun _ hp => hp)
      (fun _ hp => by
        simp only [loopN2MaxCallCallSourceFinalPostNoX1V5_unfold, r2MTTN2V5_eq, r1MTTN2V5_eq] at hp
        unfold loopN2UnifiedPostV5NoX1
        simp only [r2MTTN2V5_eq, r1MTTN2V5_eq]
        xperm_hyp hp)
      (divK_loop_n2_max_call_call_from_source_exact_loopIterScratch_v5_noNop
        sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old raVal
        retMem dMem dloMem scratchUn0 scratchMem halign hconds)
  · -- TFF = TMM (call-max-max)
    have hb2 : BitVec.ult u2 v1 := hbltu_2.symm
    have hb1 : ¬BitVec.ult (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1 v1 := by
      simp only at hbltu_1; rw [show BitVec.ult _ v1 = false from hbltu_1.symm]; decide
    have hb0 : ¬BitVec.ult
        (iterN2Max v0 v1 v2 v3 u0Orig1
          (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
          (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
          (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
          (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1 v1 := by
      simp only at hbltu_0; rw [show BitVec.ult _ v1 = false from hbltu_0.symm]; decide
    have hconds := loopN2CallMaxMaxSourceConds_of_selectedCarryV5
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 hb2 hb1 hb0 hcarry
    exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
      (fun _ hp => hp)
      (fun _ hp => by
        simp only [loopN2CallMaxMaxSourceFinalPostNoX1V5_unfold, r2CCCN2V5_eq, r1TMMN2V5_eq] at hp
        unfold loopN2UnifiedPostV5NoX1
        simp only [r2CCCN2V5_eq, r1TMMN2V5_eq]
        xperm_hyp hp)
      (divK_loop_n2_call_max_max_from_source_exact_loopIterScratch_v5_noNop
        sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old raVal
        retMem dMem dloMem scratchUn0 scratchMem halign hconds)
  · -- TFT = TMT (call-max-call)
    have hb2 : BitVec.ult u2 v1 := hbltu_2.symm
    have hb1 : ¬BitVec.ult (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1 v1 := by
      simp only at hbltu_1; rw [show BitVec.ult _ v1 = false from hbltu_1.symm]; decide
    have hb0 : BitVec.ult
        (iterN2Max v0 v1 v2 v3 u0Orig1
          (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.1
          (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1
          (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.1
          (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1 v1 := by
      simp only at hbltu_0; exact hbltu_0.symm
    have hconds := loopN2CallMaxCallSourceConds_of_selectedCarryV5
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 hb2 hb1 hb0 hcarry
    exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
      (fun _ hp => hp)
      (fun _ hp => by
        simp only [loopN2CallMaxCallSourceFinalPostNoX1V5_unfold, r2CCCN2V5_eq, r1TMMN2V5_eq] at hp
        unfold loopN2UnifiedPostV5NoX1
        simp only [r2CCCN2V5_eq, r1TMMN2V5_eq]
        xperm_hyp hp)
      (divK_loop_n2_call_max_call_from_source_exact_loopIterScratch_v5_noNop
        sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old raVal
        retMem dMem dloMem scratchUn0 scratchMem halign hconds)
  · -- TTF = CCM (call-call-max)
    have hb2 : BitVec.ult u2 v1 := hbltu_2.symm
    have hb1 : BitVec.ult (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1 v1 := by
      simp only at hbltu_1; exact hbltu_1.symm
    have hb0 : ¬BitVec.ult
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
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1 v1 := by
      simp only at hbltu_0; rw [show BitVec.ult _ v1 = false from hbltu_0.symm]; decide
    have hconds := loopN2CallCallMaxSourceConds_of_selectedCarryV5
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 hb2 hb1 hb0 hcarry
    exact cpsTripleWithin_mono_nSteps (by decide) <| cpsTripleWithin_weaken
      (fun _ hp => hp)
      (fun _ hp => by
        simp only [loopN2CallCallMaxSourceFinalPostNoX1V5_unfold, r2CCCN2V5_eq, r1CCCN2V5_eq] at hp
        unfold loopN2UnifiedPostV5NoX1
        simp only [r2CCCN2V5_eq, r1CCCN2V5_eq]
        xperm_hyp hp)
      (divK_loop_n2_call_call_max_from_source_exact_loopIterScratch_v5_noNop
        sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old raVal
        retMem dMem dloMem scratchUn0 scratchMem halign hconds)
  · -- TTT = CCC (all call)
    have hb2 : BitVec.ult u2 v1 := hbltu_2.symm
    have hb1 : BitVec.ult (iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1)
        v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.1 v1 := by
      simp only at hbltu_1; exact hbltu_1.symm
    have hb0 : BitVec.ult
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
            v0 v1 v2 v3 u0 u1 u2 u3 uTop).2.2.2.2.1).2.2.1 v1 := by
      simp only at hbltu_0; exact hbltu_0.symm
    have hconds := loopN2CallCallCallSourceConds_of_selectedCarryV5
      v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 hb2 hb1 hb0 hcarry
    exact cpsTripleWithin_weaken
      (fun _ hp => hp)
      (fun _ hp => by
        simp only [loopN2CallCallCallSourceFinalPostNoX1V5_unfold, r2CCCN2V5_eq, r1CCCN2V5_eq] at hp
        unfold loopN2UnifiedPostV5NoX1
        simp only [r2CCCN2V5_eq, r1CCCN2V5_eq]
        xperm_hyp hp)
      (divK_loop_n2_call_call_call_from_source_exact_loopIterScratch_v5_noNop
        sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
        v0 v1 v2 v3 u0 u1 u2 u3 uTop u0Orig1 u0Orig0 q2Old q1Old q0Old raVal
        retMem dMem dloMem scratchUn0 scratchMem halign hconds)

end EvmAsm.Evm64
