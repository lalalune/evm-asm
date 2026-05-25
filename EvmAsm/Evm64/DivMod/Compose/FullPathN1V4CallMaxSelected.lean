import EvmAsm.Evm64.DivMod.Compose.FullPathN1V4

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Selected-only assumptions for the bundled N1 call/max/max/max input
    path. Unlike `loopN1CallMaxmaxmaxExactInputHypotheses`, this package
    does not carry a universal `Carry2NzAll` premise. -/
@[irreducible]
def loopN1CallMaxmaxmaxSelectedInputHypotheses
    (I : LoopN1CallMaxmaxmaxExactInputs) : Prop :=
  BitVec.ult I.u1 I.v0 ∧
  loopN1CallMaxmaxmaxBranchFacts
    I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop I.u0Orig2 I.u0Orig1 ∧
  loopN1CallMaxmaxmaxSelectedCarryFacts
    I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
    I.u0Orig2 I.u0Orig1 I.u0Orig0

/-- Compatibility projection from the old exact-hypotheses bundle to the
    selected-only input package. -/
theorem loopN1CallMaxmaxmaxSelectedInputHypotheses_of_exact
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (hh : loopN1CallMaxmaxmaxExactInputHypotheses I) :
    loopN1CallMaxmaxmaxSelectedInputHypotheses I := by
  unfold loopN1CallMaxmaxmaxSelectedInputHypotheses
  exact ⟨loopN1CallMaxmaxmaxExactInputHypotheses_hbltu3 I hh,
    loopN1CallMaxmaxmaxExactInputHypotheses_branches I hh,
    loopN1CallMaxmaxmaxExactInputHypotheses_selectedCarry I hh⟩

theorem loopN1CallMaxmaxmaxSelectedInputHypotheses_hbltu3
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (hh : loopN1CallMaxmaxmaxSelectedInputHypotheses I) :
    BitVec.ult I.u1 I.v0 := by
  unfold loopN1CallMaxmaxmaxSelectedInputHypotheses at hh
  exact hh.1

theorem loopN1CallMaxmaxmaxSelectedInputHypotheses_branches
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (hh : loopN1CallMaxmaxmaxSelectedInputHypotheses I) :
    loopN1CallMaxmaxmaxBranchFacts
      I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop I.u0Orig2 I.u0Orig1 := by
  unfold loopN1CallMaxmaxmaxSelectedInputHypotheses at hh
  exact hh.2.1

theorem loopN1CallMaxmaxmaxSelectedInputHypotheses_hbltu2
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (hh : loopN1CallMaxmaxmaxSelectedInputHypotheses I) :
    ¬BitVec.ult
      (loopN1CallMaxmaxmaxR3 I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop).2.1
      I.v0 := by
  exact loopN1CallMaxmaxmaxBranchFacts_hbltu2
    I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop I.u0Orig2 I.u0Orig1
    (loopN1CallMaxmaxmaxSelectedInputHypotheses_branches I hh)

theorem loopN1CallMaxmaxmaxSelectedInputHypotheses_hbltu1
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (hh : loopN1CallMaxmaxmaxSelectedInputHypotheses I) :
    ¬BitVec.ult
      (loopN1CallMaxmaxmaxR2 I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
        I.u0Orig2).2.1 I.v0 := by
  exact loopN1CallMaxmaxmaxBranchFacts_hbltu1
    I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop I.u0Orig2 I.u0Orig1
    (loopN1CallMaxmaxmaxSelectedInputHypotheses_branches I hh)

theorem loopN1CallMaxmaxmaxSelectedInputHypotheses_hbltu0
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (hh : loopN1CallMaxmaxmaxSelectedInputHypotheses I) :
    ¬BitVec.ult
      (loopN1CallMaxmaxmaxR1 I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
        I.u0Orig2 I.u0Orig1).2.1 I.v0 := by
  exact loopN1CallMaxmaxmaxBranchFacts_hbltu0
    I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop I.u0Orig2 I.u0Orig1
    (loopN1CallMaxmaxmaxSelectedInputHypotheses_branches I hh)

theorem loopN1CallMaxmaxmaxSelectedInputHypotheses_selectedCarry
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (hh : loopN1CallMaxmaxmaxSelectedInputHypotheses I) :
    loopN1CallMaxmaxmaxSelectedCarryFacts
      I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
      I.u0Orig2 I.u0Orig1 I.u0Orig0 := by
  unfold loopN1CallMaxmaxmaxSelectedInputHypotheses at hh
  exact hh.2.2

/-- Bundled first j=3 call-body step over the full `divCode_v4` bundle,
    from selected-only input hypotheses. -/
theorem divK_loop_n1_call_j3_exact_x1_framed_v4_input_of_selected
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (halign : loopN1CallMaxmaxmaxExactInputAligned I)
    (hh : loopN1CallMaxmaxmaxSelectedInputHypotheses I) :
    loopN1CallMaxmaxmaxJ3ExactInputSpecV4 I := by
  unfold loopN1CallMaxmaxmaxJ3ExactInputSpecV4
  exact divK_loop_n1_call_j3_exact_x1_framed_v4 I.sp I.base
    I.jOld I.v5Old I.v6Old I.v7Old I.v10Old I.v11Old I.v2Old
    I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
    I.u0Orig2 I.u0Orig1 I.u0Orig0 I.q3Old I.q2Old I.q1Old I.q0Old
    I.retMem I.dMem I.dloMem I.scratchUn0 I.scratchMem I.raVal
    (loopN1CallMaxmaxmaxExactInputAligned_raw I halign)
    (loopN1CallMaxmaxmaxSelectedInputHypotheses_hbltu3 I hh)
    (isAddbackCarry2NzN1CallV4_raw I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
      (by
        have hselected := loopN1CallMaxmaxmaxSelectedInputHypotheses_selectedCarry I hh
        unfold loopN1CallMaxmaxmaxSelectedCarryFacts at hselected
        exact hselected.1))

/-- Bundled all-max tail after the first j=3 call-body step over the full
    `divCode_v4` bundle, from selected-only input hypotheses. -/
theorem divK_loop_n1_call_iter210_exact_x1_framed_v4_input_of_selected
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (hh : loopN1CallMaxmaxmaxSelectedInputHypotheses I) :
    loopN1CallMaxmaxmaxIter210ExactInputSpecV4 I := by
  unfold loopN1CallMaxmaxmaxIter210ExactInputSpecV4
  let r3 := loopN1CallMaxmaxmaxR3 I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
  have hselected := loopN1CallMaxmaxmaxSelectedInputHypotheses_selectedCarry I hh
  unfold loopN1CallMaxmaxmaxSelectedCarryFacts at hselected
  obtain ⟨_hcall, hcarry2_j2, hcarry2_j1, hcarry2_j0⟩ := hselected
  exact cpsTripleWithin_divCode_noNop_v4_to_divCode_v4
    (divK_loop_n1_iter210_maxmaxmax_exact_x1_v4_noNop_selected_carry I.sp I.base
    I.jOld I.v5Old I.v6Old I.v7Old I.v10Old I.v11Old I.v2Old
    I.v0 I.v1 I.v2 I.v3
    I.u0Orig2 r3.2.1 r3.2.2.1 r3.2.2.2.1 r3.2.2.2.2.1
    I.u0Orig1 I.u0Orig0 I.q2Old I.q1Old I.q0Old
    (I.base + div128CallRetOff) I.v0 (divKTrialCallV4DLo I.v0)
    (divKTrialCallV4Un0 I.u0) I.raVal
    (by
      dsimp only [r3]
      exact loopN1CallMaxmaxmaxSelectedInputHypotheses_hbltu2 I hh)
    (by
      dsimp only [r3]
      have h := loopN1CallMaxmaxmaxSelectedInputHypotheses_hbltu1 I hh
      unfold loopN1CallMaxmaxmaxR2 at h
      exact h)
    (by
      dsimp only [r3]
      have h := loopN1CallMaxmaxmaxSelectedInputHypotheses_hbltu0 I hh
      unfold loopN1CallMaxmaxmaxR1 at h
      unfold loopN1CallMaxmaxmaxR2 at h
      exact h)
    (by
      dsimp only [r3]
      exact hcarry2_j2)
    (by
      dsimp only [r3]
      unfold loopN1CallMaxmaxmaxR2 at hcarry2_j1
      exact hcarry2_j1)
    (by
      dsimp only [r3]
      unfold loopN1CallMaxmaxmaxR1 at hcarry2_j0
      unfold loopN1CallMaxmaxmaxR2 at hcarry2_j0
      exact hcarry2_j0))

/-- Bundled framed all-max tail pre/post over the full `divCode_v4` bundle,
    from selected-only input hypotheses. -/
theorem divK_loop_n1_call_iter210_framed_prepost_exact_x1_v4_input_of_selected
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (hh : loopN1CallMaxmaxmaxSelectedInputHypotheses I) :
    cpsTripleWithin 556 (I.base + loopBodyOff) (I.base + denormOff)
      (divCode_v4 I.base)
      (loopN1CallMaxmaxmaxIter210FramedPreInput I)
      (loopN1CallMaxmaxmaxIter210FramedPostInput I) := by
  unfold loopN1CallMaxmaxmaxIter210FramedPreInput
    loopN1CallMaxmaxmaxIter210FramedPostInput
  let r3 := loopN1CallMaxmaxmaxR3 I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
  let c3 := (mulsubN4 (divKTrialCallV4QHat I.u1 I.u0 I.v0)
    I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3).2.2.2.2
  let uBase3 := I.sp + signExtend12 4056 - (3 : Word) <<< (3 : BitVec 6).toNat
  let qAddr3 := I.sp + signExtend12 4088 - (3 : Word) <<< (3 : BitVec 6).toNat
  have hselected := loopN1CallMaxmaxmaxSelectedInputHypotheses_selectedCarry I hh
  unfold loopN1CallMaxmaxmaxSelectedCarryFacts at hselected
  obtain ⟨_hcall, hcarry2_j2, hcarry2_j1, hcarry2_j0⟩ := hselected
  have H210 := cpsTripleWithin_divCode_noNop_v4_to_divCode_v4
    (divK_loop_n1_iter210_maxmaxmax_exact_x1_v4_noNop_selected_carry I.sp I.base
    (3 : Word) ((3 : Word) <<< (3 : BitVec 6).toNat) uBase3 qAddr3 c3 r3.1
    r3.2.2.2.2.1
    I.v0 I.v1 I.v2 I.v3
    I.u0Orig2 r3.2.1 r3.2.2.1 r3.2.2.2.1 r3.2.2.2.2.1
    I.u0Orig1 I.u0Orig0 I.q2Old I.q1Old I.q0Old
    (I.base + div128CallRetOff) I.v0 (divKTrialCallV4DLo I.v0)
    (divKTrialCallV4Un0 I.u0) I.raVal
    (by
      dsimp only [r3]
      exact loopN1CallMaxmaxmaxSelectedInputHypotheses_hbltu2 I hh)
    (by
      dsimp only [r3]
      have h := loopN1CallMaxmaxmaxSelectedInputHypotheses_hbltu1 I hh
      unfold loopN1CallMaxmaxmaxR2 at h
      exact h)
    (by
      dsimp only [r3]
      have h := loopN1CallMaxmaxmaxSelectedInputHypotheses_hbltu0 I hh
      unfold loopN1CallMaxmaxmaxR1 at h
      unfold loopN1CallMaxmaxmaxR2 at h
      exact h)
    (by
      dsimp only [r3]
      exact hcarry2_j2)
    (by
      dsimp only [r3]
      unfold loopN1CallMaxmaxmaxR2 at hcarry2_j1
      exact hcarry2_j1)
    (by
      dsimp only [r3]
      unfold loopN1CallMaxmaxmaxR1 at hcarry2_j0
      unfold loopN1CallMaxmaxmaxR2 at hcarry2_j0
      exact hcarry2_j0))
  have H210f := cpsTripleWithin_frameR
    (loopN1CallMaxmaxmaxIter210FrameInput I) (by pcFree) H210
  exact H210f

/-- Framed all-max tail from the actual bundled j=3 post to the final N1
    call/max/max/max scratch post over the full `divCode_v4` bundle, from
    selected-only input hypotheses. -/
theorem divK_loop_n1_call_iter210_framed_exact_x1_v4_input_of_selected
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (hh : loopN1CallMaxmaxmaxSelectedInputHypotheses I) :
    cpsTripleWithin 556 (I.base + loopBodyOff) (I.base + denormOff)
      (divCode_v4 I.base)
      (loopN1CallMaxmaxmaxJ3PostInput I)
      (loopN1CallMaxmaxmaxScratchPostNoX1 I.sp I.base
        I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
        I.u0Orig2 I.u0Orig1 I.u0Orig0 I.scratchMem ** (.x1 ↦ᵣ I.raVal)) := by
  exact cpsTripleWithin_weaken
    (loopN1CallMaxmaxmaxJ3PostInput_to_iter210FramedPre I)
    (loopN1CallMaxmaxmaxIter210FramedPostInput_to_scratchPost I)
    (divK_loop_n1_call_iter210_framed_prepost_exact_x1_v4_input_of_selected I hh)

/-- Bundled first j=3 call-body step over the full `divCode_v4` bundle,
    using the selected call carry from the bundled path facts. -/
theorem divK_loop_n1_call_j3_exact_x1_framed_v4_input_selected_carry
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (halign : loopN1CallMaxmaxmaxExactInputAligned I)
    (hh : loopN1CallMaxmaxmaxExactInputHypotheses I) :
    loopN1CallMaxmaxmaxJ3ExactInputSpecV4 I := by
  unfold loopN1CallMaxmaxmaxJ3ExactInputSpecV4
  exact divK_loop_n1_call_j3_exact_x1_framed_v4 I.sp I.base
    I.jOld I.v5Old I.v6Old I.v7Old I.v10Old I.v11Old I.v2Old
    I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
    I.u0Orig2 I.u0Orig1 I.u0Orig0 I.q3Old I.q2Old I.q1Old I.q0Old
    I.retMem I.dMem I.dloMem I.scratchUn0 I.scratchMem I.raVal
    (loopN1CallMaxmaxmaxExactInputAligned_raw I halign)
    (loopN1CallMaxmaxmaxExactInputHypotheses_hbltu3 I hh)
    (isAddbackCarry2NzN1CallV4_raw I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
      (by
        have hselected := loopN1CallMaxmaxmaxExactInputHypotheses_selectedCarry I hh
        unfold loopN1CallMaxmaxmaxSelectedCarryFacts at hselected
        exact hselected.1))

/-- Bundled all-max tail after the first j=3 call-body step over the full
    `divCode_v4` bundle, routed through the selected-carry no-NOP wrapper. -/
theorem divK_loop_n1_call_iter210_exact_x1_framed_v4_input_selected_carry
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (hh : loopN1CallMaxmaxmaxExactInputHypotheses I) :
    loopN1CallMaxmaxmaxIter210ExactInputSpecV4 I := by
  unfold loopN1CallMaxmaxmaxIter210ExactInputSpecV4
  have H := divK_loop_n1_call_iter210_exact_x1_framed_v4_noNop_input I hh
  unfold loopN1CallMaxmaxmaxIter210ExactInputSpec at H
  exact cpsTripleWithin_divCode_noNop_v4_to_divCode_v4
    H

/-- Bundled framed all-max tail pre/post over the full `divCode_v4` bundle,
    routed through the selected-carry no-NOP wrapper. -/
theorem divK_loop_n1_call_iter210_framed_prepost_exact_x1_v4_input_selected_carry
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (hh : loopN1CallMaxmaxmaxExactInputHypotheses I) :
    cpsTripleWithin 556 (I.base + loopBodyOff) (I.base + denormOff)
      (divCode_v4 I.base)
      (loopN1CallMaxmaxmaxIter210FramedPreInput I)
      (loopN1CallMaxmaxmaxIter210FramedPostInput I) := by
  exact cpsTripleWithin_divCode_noNop_v4_to_divCode_v4
    (divK_loop_n1_call_iter210_framed_prepost_exact_x1_v4_noNop_input I hh)

/-- Framed all-max tail from the actual bundled j=3 post to the final N1
    call/max/max/max scratch post over the full `divCode_v4` bundle, routed
    through the selected-carry no-NOP wrapper. -/
theorem divK_loop_n1_call_iter210_framed_exact_x1_v4_input_selected_carry
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (hh : loopN1CallMaxmaxmaxExactInputHypotheses I) :
    cpsTripleWithin 556 (I.base + loopBodyOff) (I.base + denormOff)
      (divCode_v4 I.base)
      (loopN1CallMaxmaxmaxJ3PostInput I)
      (loopN1CallMaxmaxmaxScratchPostNoX1 I.sp I.base
        I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
        I.u0Orig2 I.u0Orig1 I.u0Orig0 I.scratchMem ** (.x1 ↦ᵣ I.raVal)) := by
  have H := divK_loop_n1_call_iter210_framed_exact_x1_v4_noNop_input I hh
  unfold loopN1CallMaxmaxmaxIter210FramedExactInputSpec at H
  exact cpsTripleWithin_divCode_noNop_v4_to_divCode_v4
    H

end EvmAsm.Evm64
