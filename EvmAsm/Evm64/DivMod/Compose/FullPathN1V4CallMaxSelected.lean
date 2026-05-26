import EvmAsm.Evm64.DivMod.Compose.FullPathN1V4

namespace EvmAsm.Evm64

open EvmAsm.Rv64

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
