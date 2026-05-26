/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN1V4NoNopSelectedIfBorrow

  No-NOP selected-if-borrow wrappers for the n=1 v4 call/max/max/max path.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN1V4CallMaxSelectedIfBorrow
import EvmAsm.Evm64.DivMod.Compose.FullPathN1V4NoNopCallMaxInput

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Bundled first j=3 call-body step over `divCode_noNop_v4`, using the
    selected-if-borrow input hypothesis surface. -/
theorem divK_loop_n1_call_j3_exact_x1_framed_v4_noNop_input_of_selected_if_borrow
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (halign : loopN1CallMaxmaxmaxExactInputAligned I)
    (hh : loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses I) :
    loopN1CallMaxmaxmaxJ3ExactInputSpec I := by
  unfold loopN1CallMaxmaxmaxJ3ExactInputSpec
  exact divK_loop_n1_call_j3_exact_x1_framed_v4_noNop I.sp I.base
    I.jOld I.v5Old I.v6Old I.v7Old I.v10Old I.v11Old I.v2Old
    I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
    I.u0Orig2 I.u0Orig1 I.u0Orig0 I.q3Old I.q2Old I.q1Old I.q0Old
    I.retMem I.dMem I.dloMem I.scratchUn0 I.scratchMem I.raVal
    (loopN1CallMaxmaxmaxExactInputAligned_raw I halign)
    (loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses_hbltu3 I hh)
    (isAddbackCarry2NzN1CallV4_raw I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
      (loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses_carryIfBorrowCall I hh))

/-- Bundled all-max tail after the first j=3 call-body step over
    `divCode_noNop_v4`, using selected-if-borrow input hypotheses. -/
theorem divK_loop_n1_call_iter210_exact_x1_framed_v4_noNop_input_of_selected_if_borrow_input
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (hh : loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses I) :
    loopN1CallMaxmaxmaxIter210ExactInputSpec I := by
  unfold loopN1CallMaxmaxmaxIter210ExactInputSpec
  let r3 := loopN1CallMaxmaxmaxR3 I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
  exact divK_loop_n1_iter210_maxmaxmax_exact_x1_v4_noNop_selected_carry_if_borrow I.sp I.base
    I.jOld I.v5Old I.v6Old I.v7Old I.v10Old I.v11Old I.v2Old
    I.v0 I.v1 I.v2 I.v3
    I.u0Orig2 r3.2.1 r3.2.2.1 r3.2.2.2.1 r3.2.2.2.2.1
    I.u0Orig1 I.u0Orig0 I.q2Old I.q1Old I.q0Old
    (I.base + div128CallRetOff) I.v0 (divKTrialCallV4DLo I.v0)
    (divKTrialCallV4Un0 I.u0) I.raVal
    (by
      dsimp only [r3]
      exact loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses_hbltu2 I hh)
    (by
      dsimp only [r3]
      have h := loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses_hbltu1 I hh
      unfold loopN1CallMaxmaxmaxR2 at h
      exact h)
    (by
      dsimp only [r3]
      have h := loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses_hbltu0 I hh
      unfold loopN1CallMaxmaxmaxR1 at h
      unfold loopN1CallMaxmaxmaxR2 at h
      exact h)
    (by
      dsimp only [r3]
      have h := loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses_carryIfBorrowMax2 I hh
      unfold selectedN1MaxCarryIfBorrow at h
      exact h)
    (by
      dsimp only [r3]
      have h := loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses_carryIfBorrowMax1 I hh
      unfold loopN1CallMaxmaxmaxR2 at h
      unfold selectedN1MaxCarryIfBorrow at h
      exact h)
    (by
      dsimp only [r3]
      have h := loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses_carryIfBorrowMax0 I hh
      unfold loopN1CallMaxmaxmaxR1 at h
      unfold loopN1CallMaxmaxmaxR2 at h
      unfold selectedN1MaxCarryIfBorrow at h
      exact h)

/-- Bundled framed all-max tail pre/post over `divCode_noNop_v4`, using
    selected-if-borrow input hypotheses. -/
theorem divK_loop_n1_call_iter210_framed_prepost_exact_x1_v4_noNop_input_of_selected_if_borrow_input
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (hh : loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses I) :
    cpsTripleWithin 556 (I.base + loopBodyOff) (I.base + denormOff)
      (divCode_noNop_v4 I.base)
      (loopN1CallMaxmaxmaxIter210FramedPreInput I)
      (loopN1CallMaxmaxmaxIter210FramedPostInput I) := by
  unfold loopN1CallMaxmaxmaxIter210FramedPreInput
    loopN1CallMaxmaxmaxIter210FramedPostInput
  let r3 := loopN1CallMaxmaxmaxR3 I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3 I.uTop
  let c3 := (mulsubN4 (divKTrialCallV4QHat I.u1 I.u0 I.v0)
    I.v0 I.v1 I.v2 I.v3 I.u0 I.u1 I.u2 I.u3).2.2.2.2
  let uBase3 := I.sp + signExtend12 4056 - (3 : Word) <<< (3 : BitVec 6).toNat
  let qAddr3 := I.sp + signExtend12 4088 - (3 : Word) <<< (3 : BitVec 6).toNat
  have H210 := divK_loop_n1_iter210_maxmaxmax_exact_x1_v4_noNop_selected_carry_if_borrow
    I.sp I.base
    (3 : Word) ((3 : Word) <<< (3 : BitVec 6).toNat) uBase3 qAddr3 c3 r3.1
    r3.2.2.2.2.1
    I.v0 I.v1 I.v2 I.v3
    I.u0Orig2 r3.2.1 r3.2.2.1 r3.2.2.2.1 r3.2.2.2.2.1
    I.u0Orig1 I.u0Orig0 I.q2Old I.q1Old I.q0Old
    (I.base + div128CallRetOff) I.v0 (divKTrialCallV4DLo I.v0)
    (divKTrialCallV4Un0 I.u0) I.raVal
    (by
      dsimp only [r3]
      exact loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses_hbltu2 I hh)
    (by
      dsimp only [r3]
      have h := loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses_hbltu1 I hh
      unfold loopN1CallMaxmaxmaxR2 at h
      exact h)
    (by
      dsimp only [r3]
      have h := loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses_hbltu0 I hh
      unfold loopN1CallMaxmaxmaxR1 at h
      unfold loopN1CallMaxmaxmaxR2 at h
      exact h)
    (by
      dsimp only [r3]
      have h := loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses_carryIfBorrowMax2 I hh
      unfold selectedN1MaxCarryIfBorrow at h
      exact h)
    (by
      dsimp only [r3]
      have h := loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses_carryIfBorrowMax1 I hh
      unfold loopN1CallMaxmaxmaxR2 at h
      unfold selectedN1MaxCarryIfBorrow at h
      exact h)
    (by
      dsimp only [r3]
      have h := loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses_carryIfBorrowMax0 I hh
      unfold loopN1CallMaxmaxmaxR1 at h
      unfold loopN1CallMaxmaxmaxR2 at h
      unfold selectedN1MaxCarryIfBorrow at h
      exact h)
  have H210f := cpsTripleWithin_frameR
    (loopN1CallMaxmaxmaxIter210FrameInput I) (by pcFree) H210
  exact H210f

/-- Framed all-max tail from the actual bundled j=3 post to the final N1
    call/max/max/max scratch post over `divCode_noNop_v4`, using
    selected-if-borrow input hypotheses. -/
theorem divK_loop_n1_call_iter210_framed_exact_x1_v4_noNop_input_of_selected_if_borrow_input
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (hh : loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses I) :
    loopN1CallMaxmaxmaxIter210FramedExactInputSpec I := by
  unfold loopN1CallMaxmaxmaxIter210FramedExactInputSpec
  exact cpsTripleWithin_weaken
    (loopN1CallMaxmaxmaxJ3PostInput_to_iter210FramedPre I)
    (loopN1CallMaxmaxmaxIter210FramedPostInput_to_scratchPost I)
    (divK_loop_n1_call_iter210_framed_prepost_exact_x1_v4_noNop_input_of_selected_if_borrow_input I hh)

/-- Full bundled N1 call/max/max/max exact path over `divCode_noNop_v4`,
    using selected-if-borrow input hypotheses. -/
theorem divK_loop_n1_call_maxmaxmax_exact_x1_scratch_input_v4_noNop_of_selected_if_borrow_input
    (I : LoopN1CallMaxmaxmaxExactInputs)
    (halign : loopN1CallMaxmaxmaxExactInputAligned I)
    (hh : loopN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses I) :
    loopN1CallMaxmaxmaxExactInputSpec I := by
  unfold loopN1CallMaxmaxmaxExactInputSpec
  unfold loopN1CallMaxmaxmaxExactX1ScratchSpec
  have J3 := divK_loop_n1_call_j3_exact_x1_framed_v4_noNop_input_of_selected_if_borrow
    I halign hh
  unfold loopN1CallMaxmaxmaxJ3ExactInputSpec at J3
  have Htail := divK_loop_n1_call_iter210_framed_exact_x1_v4_noNop_input_of_selected_if_borrow_input
    I hh
  unfold loopN1CallMaxmaxmaxIter210FramedExactInputSpec at Htail
  exact cpsTripleWithin_seq_perm_same_cr
    (fun h hp => by
      unfold loopN1CallMaxmaxmaxJ3PostInput
      exact hp)
    J3 Htail

/-- Final exact path for the canonical full-DIV n=1 call/max/max/max bundled
    inputs over `divCode_noNop_v4`, using the selected-if-borrow input
    hypothesis surface. -/
theorem fullDivN1_call_maxmaxmax_exact_x1_scratch_v4_noNop_of_selected_if_borrow_input
    (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal : Word)
    (halign : fullDivN1CallMaxmaxmaxExactInputAligned sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      a0 a1 a2 a3 b0 b1 b2 b3
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal)
    (hh : fullDivN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      a0 a1 a2 a3 b0 b1 b2 b3
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal) :
    fullDivN1CallMaxmaxmaxExactInputSpec sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      a0 a1 a2 a3 b0 b1 b2 b3
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal := by
  unfold fullDivN1CallMaxmaxmaxExactInputSpec
  unfold fullDivN1CallMaxmaxmaxExactInputAligned at halign
  unfold fullDivN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses at hh
  exact divK_loop_n1_call_maxmaxmax_exact_x1_scratch_input_v4_noNop_of_selected_if_borrow_input
    (fullDivN1CallMaxmaxmaxExactInputs sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      a0 a1 a2 a3 b0 b1 b2 b3
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal)
    halign hh

end EvmAsm.Evm64
