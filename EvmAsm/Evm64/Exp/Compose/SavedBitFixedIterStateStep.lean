/-
  EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterStateStep

  State-count-aware wrappers for one fixed EXP iteration.
-/

import EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterStepBounds

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

/-- Repackage the branch side of a fixed-loop step post from the older
    `WithControlFrame` surface to the state-carrying `WithStateFrame` surface.
    Reload-pointer branches remain as residuals because they still need their
    reload block before re-entering the next iteration precondition. -/
theorem expTwoMulFixedIterStepPostNWithControlFrame_branchState_or_reload
    {baseWord exponentWord : EvmWord} {k : Nat}
    {iterCount e controlC6 ptr nextLimb nextNextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {frame : Assertion} {ps : PartialState}
    (hk : k < 256)
    (hCount : expTwoMulFixedIterCountInvariant k iterCount)
    (h :
      expTwoMulFixedIterStepPostNWithControlFrame k baseWord exponentWord
        iterCount e controlC6 ptr nextLimb nextNextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base frame ps) :
    (∃ bit v6 v7 v10 v11 d0 d1 d2 d3,
      let outW := expTwoMulFixedBranchResult bit
        a0 a1 a2 a3 r0 r1 r2 r3
      expTwoMulFixedIterPreNWithStateFrame (k + 1) baseWord exponentWord
        (controlC6 + signExtend12 (-1 : BitVec 12))
        (e <<< (1 : BitVec 6).toNat)
        v6
        (expTwoMulIterCountNew iterCount)
        v10
        ((e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12))
        ptr nextLimb sp evmSp
        (outW.getLimbN 3)
        (expTwoMulFixedBranchReturnPc bit base)
        (outW.getLimbN 0) (outW.getLimbN 1) (outW.getLimbN 2)
        (outW.getLimbN 3)
        d0 d1 d2 d3
        (outW.getLimbN 0) (outW.getLimbN 1) (outW.getLimbN 2)
        (outW.getLimbN 3)
        a0 a1 a2 a3 v7 v11
        frame ps) ∨
    (∃ bit v6 v7 v10 v11 d0 d1 d2 d3,
      expTwoMulFixedReloadBranchResidualWithControlFrame bit (k := k)
        baseWord exponentWord iterCount e controlC6 ptr nextLimb
        nextNextLimb sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base
        v6 v7 v10 v11 d0 d1 d2 d3 frame ps) := by
  rcases expTwoMulFixedIterStepPostNWithControlFrame_cases h with
    hBranch | hReload
  · rcases hBranch with ⟨bit, v6, v7, v10, v11, d0, d1, d2, d3, hPre⟩
    exact Or.inl
      ⟨bit, v6, v7, v10, v11, d0, d1, d2, d3,
        expTwoMulFixedIterPreNWithControlFrame_to_iterPreNWithStateFrame
          (expTwoMulFixedIterCountInvariant_succ hk hCount) hPre⟩
  · exact Or.inr hReload

/-- Case-loop post bridge for the fixed-loop induction: from the current
    semantic state, the loop-back post either re-enters the next state-carrying
    iteration precondition, or lands in the reload-pointer residual branch. -/
theorem expTwoMulFixedIterCaseLoopPost_branchState_or_reload
    {baseWord exponentWord : EvmWord} {k : Nat}
    {iterCount e controlC6 ptr nextLimb nextNextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {frame : Assertion} {ps : PartialState}
    (hk : k < 256)
    (hBase : baseWord = expResultWord a0 a1 a2 a3)
    (hNextNext :
      nextNextLimb = exponentWord.getLimbN (2 - (k + 1) / 64))
    (hState :
      expTwoMulFixedIterStateInvariant baseWord exponentWord k
        iterCount e controlC6 ptr nextLimb evmSp r0 r1 r2 r3)
    (h :
      (expTwoMulFixedIterCaseLoopPost iterCount e controlC6 ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base **
        frame) ps) :
    (∃ bit v6 v7 v10 v11 d0 d1 d2 d3,
      let outW := expTwoMulFixedBranchResult bit
        a0 a1 a2 a3 r0 r1 r2 r3
      expTwoMulFixedIterPreNWithStateFrame (k + 1) baseWord exponentWord
        (controlC6 + signExtend12 (-1 : BitVec 12))
        (e <<< (1 : BitVec 6).toNat)
        v6
        (expTwoMulIterCountNew iterCount)
        v10
        ((e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12))
        ptr nextLimb sp evmSp
        (outW.getLimbN 3)
        (expTwoMulFixedBranchReturnPc bit base)
        (outW.getLimbN 0) (outW.getLimbN 1) (outW.getLimbN 2)
        (outW.getLimbN 3)
        d0 d1 d2 d3
        (outW.getLimbN 0) (outW.getLimbN 1) (outW.getLimbN 2)
        (outW.getLimbN 3)
        a0 a1 a2 a3 v7 v11
        frame ps) ∨
    (∃ bit v6 v7 v10 v11 d0 d1 d2 d3,
      expTwoMulFixedReloadBranchResidualWithControlFrame bit (k := k)
        baseWord exponentWord iterCount e controlC6 ptr nextLimb
        nextNextLimb sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base
        v6 v7 v10 v11 d0 d1 d2 d3 frame ps) := by
  exact
    expTwoMulFixedIterStepPostNWithControlFrame_branchState_or_reload
      hk hState.2.2.2
      (expTwoMulFixedIterCaseLoopPost_to_stepPostNWithControlFrame
        hk hBase hState.2.1 hState.2.2.1 hNextNext hState.1 h)

/-- CPS eliminator for a fixed step post whose ordinary branch continuations
    are already stated over the state-carrying next-iteration precondition. -/
theorem cpsTripleWithin_expTwoMulFixedIterStepPostNWithControlFrame_branchState_elim
    {nSteps : Nat} {addr exit : Word} {cr : CodeReq}
    {baseWord exponentWord : EvmWord} {k : Nat}
    {iterCount e controlC6 ptr nextLimb nextNextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {frame Q : Assertion}
    (hk : k < 256)
    (hCount : expTwoMulFixedIterCountInvariant k iterCount)
    (hBranch :
      ∀ (bit : Bool)
        (v6 v7 v10 v11 d0 d1 d2 d3 : Word),
        cpsTripleWithin nSteps addr exit cr
          (let outW := expTwoMulFixedBranchResult bit
            a0 a1 a2 a3 r0 r1 r2 r3
          expTwoMulFixedIterPreNWithStateFrame (k + 1) baseWord exponentWord
            (controlC6 + signExtend12 (-1 : BitVec 12))
            (e <<< (1 : BitVec 6).toNat)
            v6
            (expTwoMulIterCountNew iterCount)
            v10
            ((e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12))
            ptr nextLimb sp evmSp
            (outW.getLimbN 3)
            (expTwoMulFixedBranchReturnPc bit base)
            (outW.getLimbN 0) (outW.getLimbN 1) (outW.getLimbN 2)
            (outW.getLimbN 3)
            d0 d1 d2 d3
            (outW.getLimbN 0) (outW.getLimbN 1) (outW.getLimbN 2)
            (outW.getLimbN 3)
            a0 a1 a2 a3 v7 v11
            frame)
          Q)
    (hReload :
      ∀ (bit : Bool)
        (v6 v7 v10 v11 d0 d1 d2 d3 : Word),
        cpsTripleWithin nSteps addr exit cr
          (expTwoMulFixedReloadBranchResidualWithControlFrame bit (k := k)
            baseWord exponentWord iterCount e controlC6 ptr nextLimb
            nextNextLimb sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base
            v6 v7 v10 v11 d0 d1 d2 d3 frame)
          Q) :
    cpsTripleWithin nSteps addr exit cr
      (expTwoMulFixedIterStepPostNWithControlFrame k baseWord exponentWord
        iterCount e controlC6 ptr nextLimb nextNextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base frame)
      Q :=
  cpsTripleWithin_expTwoMulFixedIterStepPostNWithControlFrame_elim
    (fun bit v6 v7 v10 v11 d0 d1 d2 d3 =>
      cpsTripleWithin_weaken
        (fun _ h =>
          expTwoMulFixedIterPreNWithControlFrame_to_iterPreNWithStateFrame
            (expTwoMulFixedIterCountInvariant_succ hk hCount) h)
        (fun _ h => h)
        (hBranch bit v6 v7 v10 v11 d0 d1 d2 d3))
    hReload

/-- CPS case-loop bridge for the fixed-loop induction.  The non-reload
    recursive edge is presented as a `WithStateFrame (k+1)` precondition;
    reload-pointer edges stay as residuals for the existing reload handlers. -/
theorem cpsTripleWithin_expTwoMulFixedIterCaseLoopPost_branchState_elim
    {nSteps : Nat} {addr exit : Word} {cr : CodeReq}
    {baseWord exponentWord : EvmWord} {k : Nat}
    {iterCount e controlC6 ptr nextLimb nextNextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {frame Q : Assertion}
    (hk : k < 256)
    (hBase : baseWord = expResultWord a0 a1 a2 a3)
    (hNextNext :
      nextNextLimb = exponentWord.getLimbN (2 - (k + 1) / 64))
    (hState :
      expTwoMulFixedIterStateInvariant baseWord exponentWord k
        iterCount e controlC6 ptr nextLimb evmSp r0 r1 r2 r3)
    (hBranch :
      ∀ (bit : Bool)
        (v6 v7 v10 v11 d0 d1 d2 d3 : Word),
        cpsTripleWithin nSteps addr exit cr
          (let outW := expTwoMulFixedBranchResult bit
            a0 a1 a2 a3 r0 r1 r2 r3
          expTwoMulFixedIterPreNWithStateFrame (k + 1) baseWord exponentWord
            (controlC6 + signExtend12 (-1 : BitVec 12))
            (e <<< (1 : BitVec 6).toNat)
            v6
            (expTwoMulIterCountNew iterCount)
            v10
            ((e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12))
            ptr nextLimb sp evmSp
            (outW.getLimbN 3)
            (expTwoMulFixedBranchReturnPc bit base)
            (outW.getLimbN 0) (outW.getLimbN 1) (outW.getLimbN 2)
            (outW.getLimbN 3)
            d0 d1 d2 d3
            (outW.getLimbN 0) (outW.getLimbN 1) (outW.getLimbN 2)
            (outW.getLimbN 3)
            a0 a1 a2 a3 v7 v11
            frame)
          Q)
    (hReload :
      ∀ (bit : Bool)
        (v6 v7 v10 v11 d0 d1 d2 d3 : Word),
        cpsTripleWithin nSteps addr exit cr
          (expTwoMulFixedReloadBranchResidualWithControlFrame bit (k := k)
            baseWord exponentWord iterCount e controlC6 ptr nextLimb
            nextNextLimb sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base
            v6 v7 v10 v11 d0 d1 d2 d3 frame)
          Q) :
    cpsTripleWithin nSteps addr exit cr
      (expTwoMulFixedIterCaseLoopPost iterCount e controlC6 ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base **
        frame)
      Q := by
  simpa [Nat.zero_add, CodeReq.union_empty_left] using
    cpsTripleWithin_seq
      (CodeReq.Disjoint.empty_left cr)
      (cpsTripleWithin_expTwoMulFixedIterCaseLoopPost_to_stepPostNWithControlFrame
        addr frame hk hBase hState.2.1 hState.2.2.1 hNextNext hState.1)
      (cpsTripleWithin_expTwoMulFixedIterStepPostNWithControlFrame_branchState_elim
        hk hState.2.2.2 hBranch hReload)

/-- Bounded one-step wrapper whose nonzero decremented-count premise comes
    from the bundled fixed-loop count invariant. -/
theorem cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_to_stepPost_of_count_bounded
    {baseWord exponentWord : EvmWord} {k : Nat}
    {nBound : Nat}
    (controlC6 e machineC6 iterCount v10 v18 ptr nextLimb
      nextNextLimb sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 : Word)
    (base : Word)
    (frame : Assertion)
    (hFrame : frame.pcFree)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hControlMachine : controlC6 = machineC6)
    (hk : k < 255)
    (hCount : expTwoMulFixedIterCountInvariant k iterCount)
    (hBase : baseWord = expResultWord a0 a1 a2 a3)
    (hNextNext :
      nextNextLimb = exponentWord.getLimbN (2 - (k + 1) / 64))
    (hBound : 193 ≤ nBound) :
    cpsTripleWithin nBound (base + 44) (base + 44)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPreNWithStateFrame k baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11 frame)
      (expTwoMulFixedIterStepPostNWithControlFrame k baseWord exponentWord
        iterCount e controlC6 ptr nextLimb nextNextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base frame) :=
  cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_to_stepPost_bounded
    controlC6 e machineC6 iterCount v10 v18 ptr nextLimb nextNextLimb
    sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
    a0 a1 a2 a3 v7 v11 base frame hFrame hbase hControlMachine
    (expTwoMulFixedIterCountInvariant_succ_ne_zero_of_lt_255 hk hCount)
    (by omega) hBase hNextNext hBound

/-- Unframed variant of
    `cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_to_stepPost_of_count_bounded`. -/
theorem cpsTripleWithin_expTwoMulFixedIterPreNWithState_to_stepPost_of_count_bounded
    {baseWord exponentWord : EvmWord} {k : Nat}
    {nBound : Nat}
    (controlC6 e machineC6 iterCount v10 v18 ptr nextLimb
      nextNextLimb sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 : Word)
    (base : Word)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hControlMachine : controlC6 = machineC6)
    (hk : k < 255)
    (hCount : expTwoMulFixedIterCountInvariant k iterCount)
    (hBase : baseWord = expResultWord a0 a1 a2 a3)
    (hNextNext :
      nextNextLimb = exponentWord.getLimbN (2 - (k + 1) / 64))
    (hBound : 193 ≤ nBound) :
    cpsTripleWithin nBound (base + 44) (base + 44)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPreNWithState k baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11)
      (expTwoMulFixedIterStepPostNWithControlFrame k baseWord exponentWord
        iterCount e controlC6 ptr nextLimb nextNextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base empAssertion) :=
  cpsTripleWithin_expTwoMulFixedIterPreNWithState_to_stepPost_bounded
    controlC6 e machineC6 iterCount v10 v18 ptr nextLimb nextNextLimb
    sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
    a0 a1 a2 a3 v7 v11 base hbase hControlMachine
    (expTwoMulFixedIterCountInvariant_succ_ne_zero_of_lt_255 hk hCount)
    (by omega) hBase hNextNext hBound

/-- Count-aware framed eliminator wrapper for one fixed EXP iteration.

    This is the eliminator counterpart of
    `cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_to_stepPost_of_count_bounded`:
    the nonzero decremented-count premise is discharged from the bundled
    count invariant, leaving the future Nat induction to provide only the
    branch/reload continuations. -/
theorem cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_stepPost_elim_of_count_bounded
    {baseWord exponentWord : EvmWord} {k : Nat}
    {nSteps nBound : Nat} {exit : Word} {frame Q : Assertion}
    (controlC6 e machineC6 iterCount v10 v18 ptr nextLimb
      nextNextLimb sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 : Word)
    (base : Word)
    (hFrame : frame.pcFree)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hControlMachine : controlC6 = machineC6)
    (hk : k < 255)
    (hCount : expTwoMulFixedIterCountInvariant k iterCount)
    (hBase : baseWord = expResultWord a0 a1 a2 a3)
    (hNextNext :
      nextNextLimb = exponentWord.getLimbN (2 - (k + 1) / 64))
    (hBound : 193 + nSteps ≤ nBound)
    (hBranch :
      ∀ (bit : Bool)
        (v6' v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin nSteps (base + 44) exit
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (let outW := expTwoMulFixedBranchResult bit
            a0 a1 a2 a3 r0 r1 r2 r3
          expTwoMulFixedIterPreNWithControlFrame (k + 1) baseWord exponentWord
            (controlC6 + signExtend12 (-1 : BitVec 12))
            (e <<< (1 : BitVec 6).toNat)
            v6'
            (expTwoMulIterCountNew iterCount)
            v10'
            ((e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12))
            ptr nextLimb sp evmSp
            (outW.getLimbN 3)
            (expTwoMulFixedBranchReturnPc bit base)
            (outW.getLimbN 0) (outW.getLimbN 1) (outW.getLimbN 2)
            (outW.getLimbN 3)
            d0' d1' d2' d3'
            (outW.getLimbN 0) (outW.getLimbN 1) (outW.getLimbN 2)
            (outW.getLimbN 3)
            a0 a1 a2 a3 v7' v11'
            frame)
          Q)
    (hReload :
      ∀ (bit : Bool)
        (v6' v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin nSteps (base + 44) exit
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expTwoMulFixedReloadBranchResidualWithControlFrame bit (k := k)
            baseWord exponentWord iterCount e controlC6 ptr nextLimb
            nextNextLimb sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base
            v6' v7' v10' v11' d0' d1' d2' d3' frame)
          Q) :
    cpsTripleWithin nBound (base + 44) exit
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPreNWithStateFrame k baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11 frame)
      Q :=
  cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_stepPost_elim_bounded
    controlC6 e machineC6 iterCount v10 v18 ptr nextLimb nextNextLimb
    sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
    a0 a1 a2 a3 v7 v11 base hFrame hbase hControlMachine
    (expTwoMulFixedIterCountInvariant_succ_ne_zero_of_lt_255 hk hCount)
    (by omega) hBase hNextNext hBound hBranch hReload

/-- Unframed variant of
    `cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_stepPost_elim_of_count_bounded`. -/
theorem cpsTripleWithin_expTwoMulFixedIterPreNWithState_stepPost_elim_of_count_bounded
    {baseWord exponentWord : EvmWord} {k : Nat}
    {nSteps nBound : Nat} {exit : Word} {Q : Assertion}
    (controlC6 e machineC6 iterCount v10 v18 ptr nextLimb
      nextNextLimb sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 : Word)
    (base : Word)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hControlMachine : controlC6 = machineC6)
    (hk : k < 255)
    (hCount : expTwoMulFixedIterCountInvariant k iterCount)
    (hBase : baseWord = expResultWord a0 a1 a2 a3)
    (hNextNext :
      nextNextLimb = exponentWord.getLimbN (2 - (k + 1) / 64))
    (hBound : 193 + nSteps ≤ nBound)
    (hBranch :
      ∀ (bit : Bool)
        (v6' v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin nSteps (base + 44) exit
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (let outW := expTwoMulFixedBranchResult bit
            a0 a1 a2 a3 r0 r1 r2 r3
          expTwoMulFixedIterPreNWithControlFrame (k + 1) baseWord exponentWord
            (controlC6 + signExtend12 (-1 : BitVec 12))
            (e <<< (1 : BitVec 6).toNat)
            v6'
            (expTwoMulIterCountNew iterCount)
            v10'
            ((e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12))
            ptr nextLimb sp evmSp
            (outW.getLimbN 3)
            (expTwoMulFixedBranchReturnPc bit base)
            (outW.getLimbN 0) (outW.getLimbN 1) (outW.getLimbN 2)
            (outW.getLimbN 3)
            d0' d1' d2' d3'
            (outW.getLimbN 0) (outW.getLimbN 1) (outW.getLimbN 2)
            (outW.getLimbN 3)
            a0 a1 a2 a3 v7' v11'
            empAssertion)
          Q)
    (hReload :
      ∀ (bit : Bool)
        (v6' v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin nSteps (base + 44) exit
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expTwoMulFixedReloadBranchResidualWithControlFrame bit (k := k)
            baseWord exponentWord iterCount e controlC6 ptr nextLimb
            nextNextLimb sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base
            v6' v7' v10' v11' d0' d1' d2' d3' empAssertion)
          Q) :
    cpsTripleWithin nBound (base + 44) exit
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPreNWithState k baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11)
      Q :=
  cpsTripleWithin_weaken
    (fun _ h => by
      rw [expTwoMulFixedIterPreNWithStateFrame_unfold, sepConj_emp_right']
      exact h)
    (fun _ h => h)
    (cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_stepPost_elim_of_count_bounded
      controlC6 e machineC6 iterCount v10 v18 ptr nextLimb nextNextLimb
      sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
      a0 a1 a2 a3 v7 v11 base (by pcFree) hbase hControlMachine
      hk hCount hBase hNextNext hBound hBranch hReload)

end EvmAsm.Evm64.Exp.Compose
