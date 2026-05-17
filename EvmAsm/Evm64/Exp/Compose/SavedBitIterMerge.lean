/-
  EvmAsm.Evm64.Exp.Compose.SavedBitIterMerge

  Branch-elimination helper for the named two-MUL saved-bit EXP iteration.
-/

import EvmAsm.Evm64.Exp.Compose.SavedBitIterPosts
import EvmAsm.Evm64.Exp.Compose.SavedBitLoopExit
import EvmAsm.Evm64.Exp.Compose.SavedBitLoopBounds

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

/-- Merge one named canonical appended-MUL EXP iteration with externally
    supplied continuations for the loop-back and loop-exit edges. This is the
    structural induction step needed by the full 256-iteration loop proof. -/
theorem exp_two_mul_named_iter_with_continuations_spec_within
    {nCont : Nat} {exit_ : Word} {R : Assertion}
    (e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 : Word)
    (base : Word)
    (hbase : base &&& 1 = 0) :
    (cpsTripleWithin nCont (base + 28) exit_
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterLoopPost (expTwoMulIterCountNew iterCount)
        (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
        (expTwoMulSquareW r0 r1 r2 r3)
        (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3))
      R) →
    (cpsTripleWithin nCont (base + 264) exit_
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterExitPost (expTwoMulIterCountNew iterCount)
        (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
        (expTwoMulSquareW r0 r1 r2 r3)
        (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3))
      R) →
    cpsTripleWithin
      (expTwoMulNamedIterStepBound + nCont)
      (base + 28)
      exit_
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterPre e iterCount v18 sp evmSp vOld r0 r1 r2 r3
        d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3)
      R := by
  intro hLoop hExit
  exact
    cpsBranchWithin_merge_same_cr
      (by
        simpa [expTwoMulIterBit, expTwoMulIterW, expTwoMulIterAw,
          expTwoMulIterRw, expTwoMulIterCountNew] using
          (exp_msb_saved_bit_two_mul_full_iter_named_pre_canonical_appended_mul_spec_within
            e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
            e0 e1 e2 e3 a0 a1 a2 a3 base hbase))
      hLoop hExit

/-- Variant of `exp_two_mul_named_iter_with_continuations_spec_within` that
    permits different bounds for the loop-back and loop-exit continuations. -/
theorem exp_two_mul_named_iter_with_continuations_max_spec_within
    {nLoop nExit : Nat} {exit_ : Word} {R : Assertion}
    (e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 : Word)
    (base : Word)
    (hbase : base &&& 1 = 0) :
    (cpsTripleWithin nLoop (base + 28) exit_
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterLoopPost (expTwoMulIterCountNew iterCount)
        (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
        (expTwoMulSquareW r0 r1 r2 r3)
        (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3))
      R) →
    (cpsTripleWithin nExit (base + 264) exit_
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterExitPost (expTwoMulIterCountNew iterCount)
        (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
        (expTwoMulSquareW r0 r1 r2 r3)
        (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3))
      R) →
    cpsTripleWithin
      (expTwoMulNamedIterStepBound + max nLoop nExit)
      (base + 28)
      exit_
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterPre e iterCount v18 sp evmSp vOld r0 r1 r2 r3
        d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3)
      R := by
  intro hLoop hExit
  exact
    exp_two_mul_named_iter_with_continuations_spec_within
      e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 base hbase
      (cpsTripleWithin_mono_nSteps (Nat.le_max_left nLoop nExit) hLoop)
      (cpsTripleWithin_mono_nSteps (Nat.le_max_right nLoop nExit) hExit)

/-- Bounded variant of
    `exp_two_mul_named_iter_with_continuations_max_spec_within`. This lets the
    future 256-step induction use a closed-form loop bound while each branch
    continuation keeps its natural local bound. -/
theorem exp_two_mul_named_iter_with_continuations_bounded_spec_within
    {nLoop nExit nBound : Nat} {exit_ : Word} {R : Assertion}
    (e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 : Word)
    (base : Word)
    (hbase : base &&& 1 = 0)
    (hBound :
      expTwoMulNamedIterStepBound + max nLoop nExit ≤ nBound) :
    (cpsTripleWithin nLoop (base + 28) exit_
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterLoopPost (expTwoMulIterCountNew iterCount)
        (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
        (expTwoMulSquareW r0 r1 r2 r3)
        (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3))
      R) →
    (cpsTripleWithin nExit (base + 264) exit_
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterExitPost (expTwoMulIterCountNew iterCount)
        (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
        (expTwoMulSquareW r0 r1 r2 r3)
        (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3))
      R) →
    cpsTripleWithin nBound
      (base + 28)
      exit_
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterPre e iterCount v18 sp evmSp vOld r0 r1 r2 r3
        d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3)
      R := by
  intro hLoop hExit
  exact
    cpsTripleWithin_mono_nSteps hBound
      (exp_two_mul_named_iter_with_continuations_max_spec_within
        e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
        e0 e1 e2 e3 a0 a1 a2 a3 base hbase hLoop hExit)

/-- Exact named-bound variant of
    `exp_two_mul_named_iter_with_continuations_max_spec_within`. -/
theorem exp_two_mul_named_iter_with_continuations_exact_named_bound_spec_within
    {nLoop nExit : Nat} {exit_ : Word} {R : Assertion}
    (e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 : Word)
    (base : Word)
    (hbase : base &&& 1 = 0) :
    (cpsTripleWithin nLoop (base + 28) exit_
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterLoopPost (expTwoMulIterCountNew iterCount)
        (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
        (expTwoMulSquareW r0 r1 r2 r3)
        (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3))
      R) →
    (cpsTripleWithin nExit (base + 264) exit_
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterExitPost (expTwoMulIterCountNew iterCount)
        (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
        (expTwoMulSquareW r0 r1 r2 r3)
        (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3))
      R) →
    cpsTripleWithin (expTwoMulNamedIterStepBound + max nLoop nExit)
      (base + 28)
      exit_
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterPre e iterCount v18 sp evmSp vOld r0 r1 r2 r3
        d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3)
      R := by
  exact
    exp_two_mul_named_iter_with_continuations_max_spec_within
      e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 base hbase

/-- Peel one named iteration from the 256-iteration body and continue with
    caller-supplied loop-back and loop-exit continuations. -/
theorem exp_two_mul_full_loop_body_peel_with_continuations_spec_within
    {nLoop nExit : Nat}
    (e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 iterCountFinal tOld out0 out1 out2 out3 : Word)
    (base : Word)
    (baseWord : EvmWord) (rest : List EvmWord) (exitCond : Prop)
    (hbase : base &&& 1 = 0)
    (hBound : expTwoMulNamedIterStepBound + max nLoop nExit ≤
      expTwoMulFullLoopBodyBound) :
    (cpsTripleWithin nLoop (base + 28) (base + 264)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterLoopPost (expTwoMulIterCountNew iterCount)
        (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
        (expTwoMulSquareW r0 r1 r2 r3)
        (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3))
      (expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
        baseWord rest exitCond)) →
    (cpsTripleWithin nExit (base + 264) (base + 264)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterExitPost (expTwoMulIterCountNew iterCount)
        (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
        (expTwoMulSquareW r0 r1 r2 r3)
        (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3))
      (expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
        baseWord rest exitCond)) →
    cpsTripleWithin expTwoMulFullLoopBodyBound (base + 28) (base + 264)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterPre e iterCount v18 sp evmSp vOld r0 r1 r2 r3
        d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3)
      (expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
        baseWord rest exitCond) := by
  exact
    exp_two_mul_named_iter_with_continuations_bounded_spec_within
      e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 base hbase hBound

/-- Closed-form variant of
    `exp_two_mul_full_loop_body_peel_with_continuations_spec_within`,
    exposing the full 256-iteration body bound as `48384` and one iteration
    as `189` steps. -/
theorem exp_two_mul_full_loop_body_peel_with_continuations_closed_bound_spec_within
    {nLoop nExit : Nat}
    (e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 iterCountFinal tOld out0 out1 out2 out3 : Word)
    (base : Word)
    (baseWord : EvmWord) (rest : List EvmWord) (exitCond : Prop)
    (hbase : base &&& 1 = 0)
    (hBound : 189 + max nLoop nExit ≤ 48384) :
    (cpsTripleWithin nLoop (base + 28) (base + 264)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterLoopPost (expTwoMulIterCountNew iterCount)
        (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
        (expTwoMulSquareW r0 r1 r2 r3)
        (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3))
      (expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
        baseWord rest exitCond)) →
    (cpsTripleWithin nExit (base + 264) (base + 264)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterExitPost (expTwoMulIterCountNew iterCount)
        (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
        (expTwoMulSquareW r0 r1 r2 r3)
        (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3))
      (expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
        baseWord rest exitCond)) →
    cpsTripleWithin 48384 (base + 28) (base + 264)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterPre e iterCount v18 sp evmSp vOld r0 r1 r2 r3
        d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3)
      (expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
        baseWord rest exitCond) := by
  intro hLoop hExit
  have hBoundNamed :
      expTwoMulNamedIterStepBound + max nLoop nExit ≤
        expTwoMulFullLoopBodyBound := by
    rw [expTwoMulNamedIterStepBound_eq, expTwoMulFullLoopBodyBound_eq]
    exact hBound
  rw [← expTwoMulFullLoopBodyBound_eq]
  exact
    exp_two_mul_full_loop_body_peel_with_continuations_spec_within
      e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 iterCountFinal tOld out0 out1 out2 out3
      base baseWord rest exitCond hbase hBoundNamed hLoop hExit

/-- Peel one named iteration from an `(iterations + 1)`-iteration body when
    both branch continuations are packaged under the `iterations`-iteration
    tail bound. -/
theorem exp_two_mul_iterations_body_peel_with_continuations_spec_within
    (iterations : Nat)
    (e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 iterCountFinal tOld out0 out1 out2 out3 : Word)
    (base : Word)
    (baseWord : EvmWord) (rest : List EvmWord) (exitCond : Prop)
    (hbase : base &&& 1 = 0) :
    (cpsTripleWithin (expTwoMulIterationsBodyBound iterations)
      (base + 28) (base + 264)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterLoopPost (expTwoMulIterCountNew iterCount)
        (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
        (expTwoMulSquareW r0 r1 r2 r3)
        (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3))
      (expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
        baseWord rest exitCond)) →
    (cpsTripleWithin (expTwoMulIterationsBodyBound iterations)
      (base + 264) (base + 264)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterExitPost (expTwoMulIterCountNew iterCount)
        (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
        (expTwoMulSquareW r0 r1 r2 r3)
        (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3))
      (expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
        baseWord rest exitCond)) →
    cpsTripleWithin (expTwoMulIterationsBodyBound (iterations + 1))
      (base + 28) (base + 264)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterPre e iterCount v18 sp evmSp vOld r0 r1 r2 r3
        d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3)
      (expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
        baseWord rest exitCond) := by
  exact
    exp_two_mul_named_iter_with_continuations_bounded_spec_within
      e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 base hbase
      (expTwoMulNamedIterStepBound_add_max_iterationsBodyBound_le_succ
        iterations)

/-- Closed-form variant of
    `exp_two_mul_iterations_body_peel_with_continuations_spec_within`,
    exposing each saved-bit two-MUL iteration as `189` steps. -/
theorem exp_two_mul_iterations_body_peel_with_continuations_closed_bound_spec_within
    (iterations : Nat)
    (e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 iterCountFinal tOld out0 out1 out2 out3 : Word)
    (base : Word)
    (baseWord : EvmWord) (rest : List EvmWord) (exitCond : Prop)
    (hbase : base &&& 1 = 0) :
    (cpsTripleWithin (iterations * 189)
      (base + 28) (base + 264)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterLoopPost (expTwoMulIterCountNew iterCount)
        (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
        (expTwoMulSquareW r0 r1 r2 r3)
        (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3))
      (expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
        baseWord rest exitCond)) →
    (cpsTripleWithin (iterations * 189)
      (base + 264) (base + 264)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterExitPost (expTwoMulIterCountNew iterCount)
        (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
        (expTwoMulSquareW r0 r1 r2 r3)
        (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3))
      (expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
        baseWord rest exitCond)) →
    cpsTripleWithin ((iterations + 1) * 189)
      (base + 28) (base + 264)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterPre e iterCount v18 sp evmSp vOld r0 r1 r2 r3
        d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3)
      (expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
        baseWord rest exitCond) := by
  intro hLoop hExit
  rw [← expTwoMulIterationsBodyBound_eq iterations] at hLoop hExit
  rw [← expTwoMulIterationsBodyBound_eq (iterations + 1)]
  exact
    exp_two_mul_iterations_body_peel_with_continuations_spec_within
      iterations
      e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 iterCountFinal tOld out0 out1 out2 out3
      base baseWord rest exitCond hbase hLoop hExit

/-- Peel one named iteration from an `(iterations + 1)`-iteration body when
    the loop-back edge is packaged under the `iterations`-iteration tail
    bound and the exit edge is discharged by a zero-step assertion bridge. -/
theorem exp_two_mul_iterations_body_peel_with_exit_imp_spec_within
    (iterations : Nat)
    (e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 iterCountFinal tOld out0 out1 out2 out3 : Word)
    (base : Word)
    (baseWord : EvmWord) (rest : List EvmWord) (exitCond : Prop)
    (hbase : base &&& 1 = 0)
    (hExit :
      ∀ hp,
        expTwoMulIterExitPost (expTwoMulIterCountNew iterCount)
          (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
          (expTwoMulSquareW r0 r1 r2 r3)
          (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3) hp →
        expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
          baseWord rest exitCond hp) :
    (cpsTripleWithin (expTwoMulIterationsBodyBound iterations)
      (base + 28) (base + 264)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterLoopPost (expTwoMulIterCountNew iterCount)
        (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
        (expTwoMulSquareW r0 r1 r2 r3)
        (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3))
      (expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
        baseWord rest exitCond)) →
    cpsTripleWithin (expTwoMulIterationsBodyBound (iterations + 1))
      (base + 28) (base + 264)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterPre e iterCount v18 sp evmSp vOld r0 r1 r2 r3
        d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3)
      (expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
        baseWord rest exitCond) := by
  intro hLoop
  exact
    exp_two_mul_named_iter_with_continuations_bounded_spec_within
      e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 base hbase
      (expTwoMulNamedIterStepBound_add_max_iterationsBodyBound_zero_le_succ
        iterations)
      hLoop
      (cpsTripleWithin_extend_code
        (hmono := by
          intro a i h
          cases h)
        (cpsTripleWithin_refl hExit))

/-- Closed-form variant of
    `exp_two_mul_iterations_body_peel_with_exit_imp_spec_within`. -/
theorem exp_two_mul_iterations_body_peel_with_exit_imp_closed_bound_spec_within
    (iterations : Nat)
    (e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 iterCountFinal tOld out0 out1 out2 out3 : Word)
    (base : Word)
    (baseWord : EvmWord) (rest : List EvmWord) (exitCond : Prop)
    (hbase : base &&& 1 = 0)
    (hExit :
      ∀ hp,
        expTwoMulIterExitPost (expTwoMulIterCountNew iterCount)
          (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
          (expTwoMulSquareW r0 r1 r2 r3)
          (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3) hp →
        expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
          baseWord rest exitCond hp) :
    (cpsTripleWithin (iterations * 189)
      (base + 28) (base + 264)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterLoopPost (expTwoMulIterCountNew iterCount)
        (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
        (expTwoMulSquareW r0 r1 r2 r3)
        (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3))
      (expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
        baseWord rest exitCond)) →
    cpsTripleWithin ((iterations + 1) * 189)
      (base + 28) (base + 264)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterPre e iterCount v18 sp evmSp vOld r0 r1 r2 r3
        d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3)
      (expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
        baseWord rest exitCond) := by
  intro hLoop
  rw [← expTwoMulIterationsBodyBound_eq iterations] at hLoop
  rw [← expTwoMulIterationsBodyBound_eq (iterations + 1)]
  exact
    exp_two_mul_iterations_body_peel_with_exit_imp_spec_within
      iterations
      e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 iterCountFinal tOld out0 out1 out2 out3
      base baseWord rest exitCond hbase hExit hLoop

/-- Convert the two concrete exit-branch postconditions into the unified
    iteration-exit postcondition expected by the bounded peel helper. -/
theorem exp_two_mul_iter_exit_post_cases_to_loop_exit_pre
    (e iterCount sp evmSp r0 r1 r2 r3 a0 a1 a2 a3
      iterCountFinal tOld out0 out1 out2 out3 : Word)
    (base : Word)
    (baseWord : EvmWord) (rest : List EvmWord) (exitCond : Prop)
    (hCondExit :
      ∀ hp,
        expTwoMulIterCondPost (expTwoMulIterCountNew iterCount)
          (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
          (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3)
          (expTwoMulIterCountNew iterCount = 0) hp →
        expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
          baseWord rest exitCond hp)
    (hSkipExit :
      ∀ hp,
        expTwoMulIterSkipPost (expTwoMulIterCountNew iterCount)
          (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
          (expTwoMulSquareW r0 r1 r2 r3)
          (expTwoMulIterCountNew iterCount = 0) hp →
        expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
          baseWord rest exitCond hp) :
    ∀ hp,
      expTwoMulIterExitPost (expTwoMulIterCountNew iterCount)
        (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
        (expTwoMulSquareW r0 r1 r2 r3)
        (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3) hp →
      expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
        baseWord rest exitCond hp := by
  intro hp hExit
  rw [expTwoMulIterExitPost_unfold] at hExit
  rcases hExit with hCond | hSkip
  · exact hCondExit hp hCond
  · exact hSkipExit hp hSkip

/-- Peel one named iteration from an `(iterations + 1)`-iteration body, reducing
    the zero-step exit bridge to the two concrete branch-postcondition cases. -/
theorem exp_two_mul_iterations_body_peel_with_exit_cases_spec_within
    (iterations : Nat)
    (e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 iterCountFinal tOld out0 out1 out2 out3 : Word)
    (base : Word)
    (baseWord : EvmWord) (rest : List EvmWord) (exitCond : Prop)
    (hbase : base &&& 1 = 0)
    (hCondExit :
      ∀ hp,
        expTwoMulIterCondPost (expTwoMulIterCountNew iterCount)
          (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
          (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3)
          (expTwoMulIterCountNew iterCount = 0) hp →
        expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
          baseWord rest exitCond hp)
    (hSkipExit :
      ∀ hp,
        expTwoMulIterSkipPost (expTwoMulIterCountNew iterCount)
          (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
          (expTwoMulSquareW r0 r1 r2 r3)
          (expTwoMulIterCountNew iterCount = 0) hp →
        expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
          baseWord rest exitCond hp) :
    (cpsTripleWithin (expTwoMulIterationsBodyBound iterations)
      (base + 28) (base + 264)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterLoopPost (expTwoMulIterCountNew iterCount)
        (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
        (expTwoMulSquareW r0 r1 r2 r3)
        (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3))
      (expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
        baseWord rest exitCond)) →
    cpsTripleWithin (expTwoMulIterationsBodyBound (iterations + 1))
      (base + 28) (base + 264)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterPre e iterCount v18 sp evmSp vOld r0 r1 r2 r3
        d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3)
      (expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
        baseWord rest exitCond) := by
  exact
    exp_two_mul_iterations_body_peel_with_exit_imp_spec_within
      iterations
      e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 iterCountFinal tOld out0 out1 out2 out3
      base baseWord rest exitCond hbase
      (exp_two_mul_iter_exit_post_cases_to_loop_exit_pre
        e iterCount sp evmSp r0 r1 r2 r3 a0 a1 a2 a3
        iterCountFinal tOld out0 out1 out2 out3 base baseWord rest exitCond
        hCondExit hSkipExit)

/-- Closed-form variant of
    `exp_two_mul_iterations_body_peel_with_exit_cases_spec_within`. -/
theorem exp_two_mul_iterations_body_peel_with_exit_cases_closed_bound_spec_within
    (iterations : Nat)
    (e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 iterCountFinal tOld out0 out1 out2 out3 : Word)
    (base : Word)
    (baseWord : EvmWord) (rest : List EvmWord) (exitCond : Prop)
    (hbase : base &&& 1 = 0)
    (hCondExit :
      ∀ hp,
        expTwoMulIterCondPost (expTwoMulIterCountNew iterCount)
          (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
          (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3)
          (expTwoMulIterCountNew iterCount = 0) hp →
        expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
          baseWord rest exitCond hp)
    (hSkipExit :
      ∀ hp,
        expTwoMulIterSkipPost (expTwoMulIterCountNew iterCount)
          (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
          (expTwoMulSquareW r0 r1 r2 r3)
          (expTwoMulIterCountNew iterCount = 0) hp →
        expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
          baseWord rest exitCond hp) :
    (cpsTripleWithin (iterations * 189)
      (base + 28) (base + 264)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterLoopPost (expTwoMulIterCountNew iterCount)
        (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
        (expTwoMulSquareW r0 r1 r2 r3)
        (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3))
      (expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
        baseWord rest exitCond)) →
    cpsTripleWithin ((iterations + 1) * 189)
      (base + 28) (base + 264)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterPre e iterCount v18 sp evmSp vOld r0 r1 r2 r3
        d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3)
      (expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
        baseWord rest exitCond) := by
  intro hLoop
  rw [← expTwoMulIterationsBodyBound_eq iterations] at hLoop
  rw [← expTwoMulIterationsBodyBound_eq (iterations + 1)]
  exact
    exp_two_mul_iterations_body_peel_with_exit_cases_spec_within
      iterations
      e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 iterCountFinal tOld out0 out1 out2 out3
      base baseWord rest exitCond hbase hCondExit hSkipExit hLoop

/-- Peel one named iteration from the 256-iteration body when both branch
    continuations are already packaged under the named 255-iteration tail
    bound. -/
theorem exp_two_mul_full_loop_body_peel_tail_with_continuations_spec_within
    (e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 iterCountFinal tOld out0 out1 out2 out3 : Word)
    (base : Word)
    (baseWord : EvmWord) (rest : List EvmWord) (exitCond : Prop)
    (hbase : base &&& 1 = 0) :
    (cpsTripleWithin expTwoMulFullLoopBodyTailBound (base + 28) (base + 264)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterLoopPost (expTwoMulIterCountNew iterCount)
        (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
        (expTwoMulSquareW r0 r1 r2 r3)
        (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3))
      (expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
        baseWord rest exitCond)) →
    (cpsTripleWithin expTwoMulFullLoopBodyTailBound (base + 264) (base + 264)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterExitPost (expTwoMulIterCountNew iterCount)
        (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
        (expTwoMulSquareW r0 r1 r2 r3)
        (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3))
      (expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
        baseWord rest exitCond)) →
    cpsTripleWithin expTwoMulFullLoopBodyBound (base + 28) (base + 264)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterPre e iterCount v18 sp evmSp vOld r0 r1 r2 r3
        d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3)
      (expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
        baseWord rest exitCond) := by
  exact
    exp_two_mul_full_loop_body_peel_with_continuations_spec_within
      e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 iterCountFinal tOld out0 out1 out2 out3
      base baseWord rest exitCond hbase
      expTwoMulNamedIterStepBound_add_max_fullTail_le_full

/-- Closed-form variant of
    `exp_two_mul_full_loop_body_peel_tail_with_continuations_spec_within`,
    using the normalized 255-iteration tail bound `48195` and full-body bound
    `48384`. -/
theorem exp_two_mul_full_loop_body_peel_tail_with_continuations_closed_bound_spec_within
    (e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 iterCountFinal tOld out0 out1 out2 out3 : Word)
    (base : Word)
    (baseWord : EvmWord) (rest : List EvmWord) (exitCond : Prop)
    (hbase : base &&& 1 = 0) :
    (cpsTripleWithin 48195 (base + 28) (base + 264)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterLoopPost (expTwoMulIterCountNew iterCount)
        (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
        (expTwoMulSquareW r0 r1 r2 r3)
        (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3))
      (expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
        baseWord rest exitCond)) →
    (cpsTripleWithin 48195 (base + 264) (base + 264)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterExitPost (expTwoMulIterCountNew iterCount)
        (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
        (expTwoMulSquareW r0 r1 r2 r3)
        (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3))
      (expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
        baseWord rest exitCond)) →
    cpsTripleWithin 48384 (base + 28) (base + 264)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterPre e iterCount v18 sp evmSp vOld r0 r1 r2 r3
        d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3)
      (expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
        baseWord rest exitCond) := by
  intro hLoop hExit
  have hLoopNamed :
      cpsTripleWithin expTwoMulFullLoopBodyTailBound (base + 28) (base + 264)
        (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
        (expTwoMulIterLoopPost (expTwoMulIterCountNew iterCount)
          (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
          (expTwoMulSquareW r0 r1 r2 r3)
          (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3))
        (expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
          baseWord rest exitCond) := by
    rw [expTwoMulFullLoopBodyTailBound_eq]
    exact hLoop
  have hExitNamed :
      cpsTripleWithin expTwoMulFullLoopBodyTailBound (base + 264) (base + 264)
        (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
        (expTwoMulIterExitPost (expTwoMulIterCountNew iterCount)
          (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
          (expTwoMulSquareW r0 r1 r2 r3)
          (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3))
        (expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
          baseWord rest exitCond) := by
    rw [expTwoMulFullLoopBodyTailBound_eq]
    exact hExit
  rw [← expTwoMulFullLoopBodyBound_eq]
  exact
    exp_two_mul_full_loop_body_peel_tail_with_continuations_spec_within
      e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 iterCountFinal tOld out0 out1 out2 out3
      base baseWord rest exitCond hbase hLoopNamed hExitNamed

/-- Peel one named iteration from the 256-iteration body with the loop-back
    continuation packaged under the named 255-iteration tail bound, reducing
    the zero-step exit bridge to the two concrete branch-postcondition cases. -/
theorem exp_two_mul_full_loop_body_peel_tail_with_exit_cases_spec_within
    (e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 iterCountFinal tOld out0 out1 out2 out3 : Word)
    (base : Word)
    (baseWord : EvmWord) (rest : List EvmWord) (exitCond : Prop)
    (hbase : base &&& 1 = 0)
    (hCondExit :
      ∀ hp,
        expTwoMulIterCondPost (expTwoMulIterCountNew iterCount)
          (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
          (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3)
          (expTwoMulIterCountNew iterCount = 0) hp →
        expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
          baseWord rest exitCond hp)
    (hSkipExit :
      ∀ hp,
        expTwoMulIterSkipPost (expTwoMulIterCountNew iterCount)
          (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
          (expTwoMulSquareW r0 r1 r2 r3)
          (expTwoMulIterCountNew iterCount = 0) hp →
        expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
          baseWord rest exitCond hp) :
    (cpsTripleWithin expTwoMulFullLoopBodyTailBound (base + 28) (base + 264)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterLoopPost (expTwoMulIterCountNew iterCount)
        (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
        (expTwoMulSquareW r0 r1 r2 r3)
        (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3))
      (expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
        baseWord rest exitCond)) →
    cpsTripleWithin expTwoMulFullLoopBodyBound (base + 28) (base + 264)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterPre e iterCount v18 sp evmSp vOld r0 r1 r2 r3
        d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3)
      (expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
        baseWord rest exitCond) := by
  intro hLoop
  rw [expTwoMulFullLoopBodyBound_eq_tail_succ]
  exact
    exp_two_mul_iterations_body_peel_with_exit_cases_spec_within
      255
      e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 iterCountFinal tOld out0 out1 out2 out3
      base baseWord rest exitCond hbase hCondExit hSkipExit hLoop

/-- Closed-form variant of
    `exp_two_mul_full_loop_body_peel_tail_with_exit_cases_spec_within`. -/
theorem exp_two_mul_full_loop_body_peel_tail_with_exit_cases_closed_bound_spec_within
    (e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 iterCountFinal tOld out0 out1 out2 out3 : Word)
    (base : Word)
    (baseWord : EvmWord) (rest : List EvmWord) (exitCond : Prop)
    (hbase : base &&& 1 = 0)
    (hCondExit :
      ∀ hp,
        expTwoMulIterCondPost (expTwoMulIterCountNew iterCount)
          (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
          (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3)
          (expTwoMulIterCountNew iterCount = 0) hp →
        expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
          baseWord rest exitCond hp)
    (hSkipExit :
      ∀ hp,
        expTwoMulIterSkipPost (expTwoMulIterCountNew iterCount)
          (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
          (expTwoMulSquareW r0 r1 r2 r3)
          (expTwoMulIterCountNew iterCount = 0) hp →
        expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
          baseWord rest exitCond hp) :
    (cpsTripleWithin 48195 (base + 28) (base + 264)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterLoopPost (expTwoMulIterCountNew iterCount)
        (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
        (expTwoMulSquareW r0 r1 r2 r3)
        (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3))
      (expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
        baseWord rest exitCond)) →
    cpsTripleWithin 48384 (base + 28) (base + 264)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterPre e iterCount v18 sp evmSp vOld r0 r1 r2 r3
        d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3)
      (expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
        baseWord rest exitCond) := by
  intro hLoop
  have hLoopNamed :
      cpsTripleWithin expTwoMulFullLoopBodyTailBound (base + 28) (base + 264)
        (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
        (expTwoMulIterLoopPost (expTwoMulIterCountNew iterCount)
          (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
          (expTwoMulSquareW r0 r1 r2 r3)
          (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3))
        (expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
          baseWord rest exitCond) := by
    rw [expTwoMulFullLoopBodyTailBound_eq]
    exact hLoop
  rw [← expTwoMulFullLoopBodyBound_eq]
  exact
    exp_two_mul_full_loop_body_peel_tail_with_exit_cases_spec_within
      e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 iterCountFinal tOld out0 out1 out2 out3
      base baseWord rest exitCond hbase hCondExit hSkipExit hLoopNamed

/-- Closed-form bound variant of
    `exp_two_mul_named_iter_with_continuations_bounded_spec_within`, using the
    normalized one-iteration cost `189`. -/
theorem exp_two_mul_named_iter_with_continuations_closed_bound_spec_within
    {nLoop nExit nBound : Nat} {exit_ : Word} {R : Assertion}
    (e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 : Word)
    (base : Word)
    (hbase : base &&& 1 = 0)
    (hBound : 189 + max nLoop nExit ≤ nBound) :
    (cpsTripleWithin nLoop (base + 28) exit_
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterLoopPost (expTwoMulIterCountNew iterCount)
        (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
        (expTwoMulSquareW r0 r1 r2 r3)
        (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3))
      R) →
    (cpsTripleWithin nExit (base + 264) exit_
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterExitPost (expTwoMulIterCountNew iterCount)
        (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
        (expTwoMulSquareW r0 r1 r2 r3)
        (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3))
      R) →
    cpsTripleWithin nBound
      (base + 28)
      exit_
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterPre e iterCount v18 sp evmSp vOld r0 r1 r2 r3
        d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3)
      R := by
  intro hLoop hExit
  exact
    exp_two_mul_named_iter_with_continuations_bounded_spec_within
      e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 base hbase
      (by simpa [expTwoMulNamedIterStepBound_eq] using hBound)
      hLoop hExit

/-- Exact closed-form bound variant of
    `exp_two_mul_named_iter_with_continuations_max_spec_within`. -/
theorem exp_two_mul_named_iter_with_continuations_exact_closed_bound_spec_within
    {nLoop nExit : Nat} {exit_ : Word} {R : Assertion}
    (e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 : Word)
    (base : Word)
    (hbase : base &&& 1 = 0) :
    (cpsTripleWithin nLoop (base + 28) exit_
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterLoopPost (expTwoMulIterCountNew iterCount)
        (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
        (expTwoMulSquareW r0 r1 r2 r3)
        (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3))
      R) →
    (cpsTripleWithin nExit (base + 264) exit_
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterExitPost (expTwoMulIterCountNew iterCount)
        (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
        (expTwoMulSquareW r0 r1 r2 r3)
        (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3))
      R) →
    cpsTripleWithin (189 + max nLoop nExit)
      (base + 28)
      exit_
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterPre e iterCount v18 sp evmSp vOld r0 r1 r2 r3
        d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3)
      R := by
  exact
    exp_two_mul_named_iter_with_continuations_closed_bound_spec_within
      e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 base hbase (by rfl)

/-- `expTwoMulIterLoopPost 0 ...` is unsatisfiable: it embeds `⌜0 ≠ 0⌝`
    (loop-back guard), so no PartialState can satisfy it. -/
theorem expTwoMulIterLoopPost_zero_count_false
    {bit sp evmSp base a0 a1 a2 a3 : Word}
    {squareW rw : EvmWord} {ps : PartialState} :
    ¬ expTwoMulIterLoopPost 0 bit sp evmSp base a0 a1 a2 a3 squareW rw ps := by
  rw [expTwoMulIterLoopPost_unfold]
  rintro (hCond | hSkip)
  · rw [expTwoMulIterCondPost_unfold] at hCond
    obtain ⟨_, _, _, _, h_tcr, _⟩ := hCond
    obtain ⟨_, _, _, _, h_triple, _⟩ := h_tcr
    obtain ⟨_, _, _, _, _, h_x0pure⟩ := h_triple
    obtain ⟨_, _, _, _, _, h_pure⟩ := h_x0pure
    exact absurd h_pure.2 (by decide)
  · rw [expTwoMulIterSkipPost_unfold] at hSkip
    obtain ⟨_, _, _, _, h_tsr, _⟩ := hSkip
    obtain ⟨_, _, _, _, h_triple, _⟩ := h_tsr
    obtain ⟨_, _, _, _, _, h_x0pure⟩ := h_triple
    obtain ⟨_, _, _, _, _, h_pure⟩ := h_x0pure
    exact absurd h_pure.2 (by decide)

/-- 0-step body spec from `expTwoMulIterLoopPost 0 ...` to anything is
    vacuously true: the precondition is unsatisfiable. -/
theorem exp_loop_body_zero_step_vacuous
    {bit sp evmSp base a0 a1 a2 a3 : Word}
    {squareW rw : EvmWord}
    {Q : Assertion} {base_ : Word}
    {code : CodeReq} :
    cpsTripleWithin 0 (base_ + 28) (base_ + 264) code
      (expTwoMulIterLoopPost 0 bit sp evmSp base a0 a1 a2 a3 squareW rw)
      Q := by
  intro R _ s _ hPR _
  exfalso
  have hP := holdsFor_sepConj_elim_left hPR
  obtain ⟨_, _, h_looppost⟩ := hP
  exact expTwoMulIterLoopPost_zero_count_false h_looppost

/-- `expTwoMulIterExitPost k ...` is unsatisfiable when `k ≠ 0`: it embeds
    `⌜k = 0⌝` (loop-exit guard), so no PartialState can satisfy it when `k ≠ 0`. -/
theorem expTwoMulIterExitPost_nonzero_count_false
    {iterCountNew : Word} (h : iterCountNew ≠ 0)
    {bit sp evmSp base a0 a1 a2 a3 : Word}
    {squareW rw : EvmWord} {ps : PartialState} :
    ¬ expTwoMulIterExitPost iterCountNew bit sp evmSp base a0 a1 a2 a3 squareW rw ps := by
  rw [expTwoMulIterExitPost_unfold]
  rintro (hCond | hSkip)
  · rw [expTwoMulIterCondPost_unfold] at hCond
    obtain ⟨_, _, _, _, h_tcr, _⟩ := hCond
    obtain ⟨_, _, _, _, h_triple, _⟩ := h_tcr
    obtain ⟨_, _, _, _, _, h_x0pure⟩ := h_triple
    obtain ⟨_, _, _, _, _, h_pure⟩ := h_x0pure
    exact absurd h_pure.2 h
  · rw [expTwoMulIterSkipPost_unfold] at hSkip
    obtain ⟨_, _, _, _, h_tsr, _⟩ := hSkip
    obtain ⟨_, _, _, _, h_triple, _⟩ := h_tsr
    obtain ⟨_, _, _, _, _, h_x0pure⟩ := h_triple
    obtain ⟨_, _, _, _, _, h_pure⟩ := h_x0pure
    exact absurd h_pure.2 h

/-- When `iterCountNew ≠ 0`, the exit post is unsatisfiable, so any implication
    `exitPost → Q` holds vacuously. This is the exit bridge for all non-final
    loop iterations in the 256-step induction. -/
theorem exp_loop_exit_vacuous_bridge
    {iterCountNew : Word} (h : iterCountNew ≠ 0)
    {bit sp evmSp base a0 a1 a2 a3 : Word} {squareW rw : EvmWord}
    {Q : PartialState → Prop} :
    ∀ ps, expTwoMulIterExitPost iterCountNew bit sp evmSp base a0 a1 a2 a3 squareW rw ps → Q ps :=
  fun _ hExit => absurd hExit (expTwoMulIterExitPost_nonzero_count_false h)

/-- Abstract n-iteration loop body spec: given any exit bridge for the current
    step's exit condition and any n-step loop-back continuation, the (n+1)-step
    body spec holds from `expTwoMulIterPre`.

    This is a thin wrapper around
    `exp_two_mul_iterations_body_peel_with_exit_imp_closed_bound_spec_within`
    that makes the "inductive step" shape explicit. -/
theorem exp_loop_body_succ_step
    (n : Nat)
    (e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 iterCountFinal tOld out0 out1 out2 out3 : Word)
    (base : Word) (baseWord : EvmWord) (rest : List EvmWord) (exitCond : Prop)
    (hbase : base &&& 1 = 0)
    (hExit : ∀ ps,
        expTwoMulIterExitPost (expTwoMulIterCountNew iterCount)
          (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
          (expTwoMulSquareW r0 r1 r2 r3)
          (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3) ps →
        expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
          baseWord rest exitCond ps)
    (hLoop : cpsTripleWithin (n * 189) (base + 28) (base + 264)
        (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
        (expTwoMulIterLoopPost (expTwoMulIterCountNew iterCount)
          (expTwoMulIterBit e) sp evmSp base a0 a1 a2 a3
          (expTwoMulSquareW r0 r1 r2 r3)
          (expTwoMulIterRw r0 r1 r2 r3 a0 a1 a2 a3))
        (expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
          baseWord rest exitCond)) :
    cpsTripleWithin ((n + 1) * 189) (base + 28) (base + 264)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulIterPre e iterCount v18 sp evmSp vOld r0 r1 r2 r3
        d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3)
      (expTwoMulLoopExitPre sp evmSp iterCountFinal tOld out0 out1 out2 out3
        baseWord rest exitCond) :=
  exp_two_mul_iterations_body_peel_with_exit_imp_closed_bound_spec_within
    n e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
    e0 e1 e2 e3 a0 a1 a2 a3 iterCountFinal tOld out0 out1 out2 out3
    base baseWord rest exitCond hbase hExit hLoop

-- Key insight for the 256-iteration loop body proof: the `loopPost` assertion
-- embeds ALL the atoms needed by the NEXT iteration's `iterPre`, except for
-- `d0..d3` which come from `memOwn` atoms (algorithmically irrelevant scratch).
--
-- For the SKIP path (bit = 0):
--   x5' = squareW.getLimbN 3  (next exponent cursor, from skipRest)
--   r0'..r3' = squareW.getLimbN 0..3  (from evmWordIs sp squareW)
--   e0'..e3' = squareW.getLimbN 0..3  (from evmWordIs (evmSp+32) squareW)
--   v18' = bit + signExtend12 0  (from skipRest's x18)
--   vOld' = (base+44)+68  (from skipRest's x1)
--   d0'..d3' = WHATEVER is at evmSp..evmSp+24  (from memOwn atoms)
--
-- For the COND path (bit = 1):
--   x5' = rw.getLimbN 3,  r0'..r3' = rw.getLimbN 0..3
--   e0'..e3' = rw.getLimbN 0..3 (from evmWordIs (evmSp+32) rw)
--   v18' = bit+signExtend12 0, vOld' = (base+152)+68
--   d0'..d3' = WHATEVER is at evmSp..evmSp+24 (from memOwn atoms)
--
-- Proving this existential bridge (expTwoMulIterLoopPost_to_iterPre_exists)
-- requires extracting d0..d3 from memOwn via Classical.choose and reassembling
-- the sepConj — see bead evm-asm-w5mk notes for the proof sketch.

/-- Bridge from `expTwoMulIterSkipPost` (the skip branch of loopPost) to
    `expTwoMulIterPre`.

    After normalizing addresses and stripping pure-fact components (which
    live in empty PartialState singletons), the skip-post and iterPre
    assertions have IDENTICAL atoms.  Each `memOwn` atom is converted to a
    concrete `memIs` via `sepConj_choose_memOwn`, and `sep_perm` closes the
    rearrangement via `ac_rfl` on `Std.Commutative`/`Std.Associative` for `**`.

    This is the `loopPost → iterPre` bridge needed to chain the peel theorem
    for the full 256-iteration loop body induction (evm-asm-w5mk). -/
theorem expTwoMulIterSkipPost_to_iterPre
    {k bit sp evmSp base a0 a1 a2 a3 : Word} {squareW : EvmWord}
    {ps : PartialState} (hk : k ≠ 0)
    (h : expTwoMulIterSkipPost k bit sp evmSp base a0 a1 a2 a3
           squareW (k ≠ 0) ps) :
    ∃ d0 d1 d2 d3,
      expTwoMulIterPre
        (squareW.getLimbN 3) k (bit + signExtend12 0) sp evmSp
        ((base + 44) + 68)
        (squareW.getLimbN 0) (squareW.getLimbN 1)
        (squareW.getLimbN 2) (squareW.getLimbN 3)
        d0 d1 d2 d3
        (squareW.getLimbN 0) (squareW.getLimbN 1)
        (squareW.getLimbN 2) (squareW.getLimbN 3)
        a0 a1 a2 a3 ps := by
  -- Unfold assertions and normalize signExtend12 addresses
  rw [expTwoMulIterSkipPost_unfold, expTwoMulIterSkipRest_unfold,
      expTwoMulIterBaseFrame_unfold] at h
  simp only [evmWordIs] at h
  simp only [signExtend12_0,
             EvmAsm.Evm64.Exp.AddrNorm.exp_se12_neg64,
             EvmAsm.Evm64.Exp.AddrNorm.exp_se12_neg56,
             EvmAsm.Evm64.Exp.AddrNorm.exp_se12_neg48,
             EvmAsm.Evm64.Exp.AddrNorm.exp_se12_neg40,
             EvmAsm.Rv64.AddrNorm.word_add_zero] at h
  -- Normalize compound address arithmetic: evmSp+32+8 → evmSp+40 etc.
  simp only [BitVec.add_assoc,
             show (32:Word) + 8 = 40 from by decide,
             show (32:Word) + 16 = 48 from by decide,
             show (32:Word) + 24 = 56 from by decide] at h
  -- Replace ⌜k≠0⌝ with empAssertion and simplify using the equation form
  rw [show (⌜k ≠ 0⌝ : Assertion) = empAssertion from
      funext fun ps' => propext ⟨fun h' => h'.1, fun h' => ⟨h', hk⟩⟩] at h
  simp only [sepConj_emp_right'] at h
  -- After simp: h contains (x18 ↦ᵣ bit) ** ⌜bit = 0⌝ ** ...
  -- Step 1: extract bit=0 as a Prop side condition
  have hbit : bit = 0 := by
    obtain ⟨_, _, _, _, houter, _⟩ := h   -- houter = OUTER (5th = left)
    obtain ⟨_, _, _, _, _, hx18rest⟩ := houter  -- hx18rest = x18 ** ⌜bit=0⌝ ** rest
    obtain ⟨_, _, _, _, _, hb0rest⟩ := hx18rest  -- hb0rest = ⌜bit=0⌝ ** rest
    exact ((sepConj_pure_left _).mp hb0rest).1
  -- Drop ⌜bit=0⌝ using the known side condition
  rw [show (⌜bit = 0⌝ : Assertion) = empAssertion from
      funext fun ps' => propext ⟨fun h' => h'.1, fun h' => ⟨h', hbit⟩⟩] at h
  simp only [sepConj_emp_left'] at h
  -- h now contains exactly the atoms of iterPre, with memOwn instead of memIs
  -- Step 2: bring each memOwn atom to front and extract d0..d3
  -- Use `apply sepConj_choose_memOwn; sep_perm h_*` which lets `sep_perm`
  -- rearrange via ac_rfl before `sepConj_choose_memOwn` extracts the value.
  -- Navigate via obtain to reach the memOwn atoms, then extract via sepConj_choose_memOwn
  obtain ⟨ps_outer, ps_bf, hd_bf, hu_bf, h_outer, h_bf⟩ := h
  obtain ⟨ps_x9x0, ps_sr, hd_sr, hu_sr, h_x9x0, h_sr⟩ := h_outer
  obtain ⟨ps_x18, ps_r1, hd1, hu1, h_x18, h_r1⟩ := h_sr
  obtain ⟨ps_x2, ps_r2, hd2, hu2, h_x2, h_r2⟩ := h_r1
  obtain ⟨ps_x12, ps_r3, hd3, hu3, h_x12, h_r3⟩ := h_r2
  obtain ⟨ps_x5, ps_r4, hd4, hu4, h_x5, h_r4⟩ := h_r3
  obtain ⟨ps_sp, ps_r5, hd5, hu5, h_sp, h_r5⟩ := h_r4
  obtain ⟨ps_e32, ps_r6, hd6, hu6, h_e32, h_r6⟩ := h_r5
  obtain ⟨ps_x6, ps_r7, hd7, hu7, h_x6, h_r7⟩ := h_r6
  obtain ⟨ps_x7, ps_r8, hd8, hu8, h_x7, h_r8⟩ := h_r7
  obtain ⟨ps_x10, ps_r9, hd9, hu9, h_x10, h_r9⟩ := h_r8
  obtain ⟨ps_x11, ps_r10, hd10, hu10, h_x11, h_r10⟩ := h_r9
  -- h_r10 : (memOwn evmSp ** memOwn(evmSp+8) ** memOwn(evmSp+16) ** memOwn(evmSp+24) ** x1) ps_r10
  obtain ⟨d0, h_d0_chain⟩ := sepConj_choose_memOwn h_r10
  obtain ⟨ps_d0, ps_r11, hd_d0, hu_d0, h_d0, h_r11⟩ := h_d0_chain
  obtain ⟨d1, h_d1_chain⟩ := sepConj_choose_memOwn h_r11
  obtain ⟨ps_d1, ps_r12, hd_d1, hu_d1, h_d1, h_r12⟩ := h_d1_chain
  obtain ⟨d2, h_d2_chain⟩ := sepConj_choose_memOwn h_r12
  obtain ⟨ps_d2, ps_r13, hd_d2, hu_d2, h_d2, h_r13⟩ := h_d2_chain
  obtain ⟨d3, h_d3_chain⟩ := sepConj_choose_memOwn h_r13
  obtain ⟨ps_d3, ps_x1, hd_d3, hu_d3, h_d3, h_x1⟩ := h_d3_chain
  -- Build h_d3_full: an assertion applied to the FULL ps using the extracted d values
  -- This is the AC-rearrangement of h with memIs atoms, applied to ps
  -- Use sep_perm on a combined hypothesis built from the components
  have h_d3_full : ((((Reg.x9 ↦ᵣ k) ** Reg.x0 ↦ᵣ 0) **
      (Reg.x18 ↦ᵣ bit) ** (Reg.x2 ↦ᵣ sp) ** (Reg.x12 ↦ᵣ evmSp) **
      (Reg.x5 ↦ᵣ squareW.getLimbN 3) **
      ((sp ↦ₘ squareW.getLimbN 0) ** (sp + 8 ↦ₘ squareW.getLimbN 1) **
       (sp + 16 ↦ₘ squareW.getLimbN 2) ** (sp + 24 ↦ₘ squareW.getLimbN 3)) **
      ((evmSp + 32 ↦ₘ squareW.getLimbN 0) ** (evmSp + 40 ↦ₘ squareW.getLimbN 1) **
       (evmSp + 48 ↦ₘ squareW.getLimbN 2) ** (evmSp + 56 ↦ₘ squareW.getLimbN 3)) **
      regOwn Reg.x6 ** regOwn Reg.x7 ** regOwn Reg.x10 ** regOwn Reg.x11 **
      (evmSp ↦ₘ d0) ** (evmSp + 8 ↦ₘ d1) ** (evmSp + 16 ↦ₘ d2) **
      (evmSp + 24 ↦ₘ d3) ** (Reg.x1 ↦ᵣ base + (44 + 68))) **
      (evmSp + 18446744073709551552 ↦ₘ a0) **
      (evmSp + 18446744073709551560 ↦ₘ a1) **
      (evmSp + 18446744073709551568 ↦ₘ a2) **
      (evmSp + 18446744073709551576 ↦ₘ a3)) ps := by
    refine ⟨ps_outer, ps_bf, hd_bf, hu_bf, ?_, h_bf⟩
    refine ⟨ps_x9x0, ps_sr, hd_sr, hu_sr, h_x9x0, ?_⟩
    refine ⟨ps_x18, ps_r1, hd1, hu1, h_x18, ?_⟩
    refine ⟨ps_x2, ps_r2, hd2, hu2, h_x2, ?_⟩
    refine ⟨ps_x12, ps_r3, hd3, hu3, h_x12, ?_⟩
    refine ⟨ps_x5, ps_r4, hd4, hu4, h_x5, ?_⟩
    refine ⟨ps_sp, ps_r5, hd5, hu5, h_sp, ?_⟩
    refine ⟨ps_e32, ps_r6, hd6, hu6, h_e32, ?_⟩
    refine ⟨ps_x6, ps_r7, hd7, hu7, h_x6, ?_⟩
    refine ⟨ps_x7, ps_r8, hd8, hu8, h_x7, ?_⟩
    refine ⟨ps_x10, ps_r9, hd9, hu9, h_x10, ?_⟩
    refine ⟨ps_x11, ps_r10, hd10, hu10, h_x11, ?_⟩
    refine ⟨ps_d0, _, hd_d0, hu_d0, h_d0, ?_⟩
    refine ⟨ps_d1, _, hd_d1, hu_d1, h_d1, ?_⟩
    refine ⟨ps_d2, _, hd_d2, hu_d2, h_d2, ?_⟩
    exact ⟨ps_d3, ps_x1, hd_d3, hu_d3, h_d3, h_x1⟩
  -- Provide witnesses and close the iterPre goal
  refine ⟨d0, d1, d2, d3, ?_⟩
  rw [expTwoMulIterPre_unfold, expTwoMulIterBaseFrame_unfold]
  simp only [signExtend12_0, signExtend12_8, signExtend12_16, signExtend12_24,
             signExtend12_32, signExtend12_40, signExtend12_48, signExtend12_56,
             EvmAsm.Evm64.Exp.AddrNorm.exp_se12_neg64,
             EvmAsm.Evm64.Exp.AddrNorm.exp_se12_neg56,
             EvmAsm.Evm64.Exp.AddrNorm.exp_se12_neg48,
             EvmAsm.Evm64.Exp.AddrNorm.exp_se12_neg40,
             EvmAsm.Rv64.AddrNorm.word_add_zero,
             BitVec.add_assoc]
  sep_perm h_d3_full

end EvmAsm.Evm64.Exp.Compose
