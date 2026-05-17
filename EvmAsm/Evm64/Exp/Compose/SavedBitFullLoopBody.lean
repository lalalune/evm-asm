/-
  EvmAsm.Evm64.Exp.Compose.SavedBitFullLoopBody

  Full-loop body composition for the 256-iteration EXP loop.

  The loop always runs exactly 256 iterations (one per bit of the exponent),
  counting down from `iterCount = 256` to 0. Each iteration:
    - Reads the current MSB of the saved exponent register `e`
    - Squares the accumulator `r`
    - If the bit is 1, also multiplies by the base `a`
    - Decrements `iterCount`

  The semantic invariant after k iterations:
    expResultWord r0..r3 = EvmWord.exp base (top k bits of exponent)
  This holds at k=0 (r = 1 = base^0) and is maintained by each iteration.
  After 256 iterations, r = EvmWord.exp base exponent.

  Architecture:
  - `expFullLoopBodyNSpec`: structural peel wrapper (sorry-free)
  - `expFullLoopBodySpec`: full 256-iter boundary using the direct loop interface
    `exp_two_mul_full_loop_boundary_of_bounded_body_spec_within` which takes:
      hLoop : expTwoMulLoopEntryPost → expTwoMulLoopExitPre
    directly, without needing the IterPre bridge.

  The remaining `sorry` is the loop invariant proof in `hLoop`:
  - Start: r = 1, iterCount = 256
  - After k iterations: r = base^(top k bits of exponent), iterCount = 256-k
  - End: r = base^exponent, iterCount = 0
  This requires 256 applications of the single-iteration spec.

  Refs: GH #92, parent evm-asm-20z6, bead evm-asm-w5mk.
  Authored by @pirapira; implemented by Claude Code.
-/

import EvmAsm.Evm64.Exp.Compose.SavedBitBoundaryLoop
import EvmAsm.Evm64.Exp.Compose.SavedBitLoopEntry
import EvmAsm.Evm64.Exp.Compose.SavedBitIterMerge
import EvmAsm.Evm64.Exp.Compose.SavedBitIterPosts
import EvmAsm.Evm64.Exp.Compose.SavedBitTwoMulCond
import EvmAsm.Evm64.EvmWordArith.Exp

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64 (Assertion CodeReq
  cpsTripleWithin cpsTripleWithin_extend_code cpsTripleWithin_weaken
  cpsTripleWithin_seq_same_cr cpsTripleWithin_mono_nSteps
  memOwn regOwn signExtend12 signExtend21)

-- ============================================================================
-- Structural peeling lemma for one iteration
-- ============================================================================

/-- Peel one iteration from an `(n+1)`-iteration body spec.  A thin wrapper
    around `exp_two_mul_iterations_body_peel_with_exit_cases_closed_bound_spec_within`
    exposing the canonical shape used in `expFullLoopBodySpec`. -/
theorem expFullLoopBodyNSpec
    (n : Nat)
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
          baseWord rest exitCond hp)
    (hTail :
      cpsTripleWithin (n * 189) (base + 28) (base + 264)
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
  exp_two_mul_iterations_body_peel_with_exit_cases_closed_bound_spec_within
    n e iterCount v18 sp evmSp vOld r0 r1 r2 r3 d0 d1 d2 d3
    e0 e1 e2 e3 a0 a1 a2 a3 iterCountFinal tOld out0 out1 out2 out3
    base baseWord rest exitCond hbase hCondExit hSkipExit hTail

-- ============================================================================
-- Full 256-iteration boundary spec
-- ============================================================================

/-- The full 256-iteration EXP boundary spec (bead evm-asm-w5mk, GH #92).

    Pre:  `expTwoMulBoundaryPre sp evmSp cOld tOld m0..m3 vOld v18 baseWord exponentWord rest`
    Post: `expTwoMulLoopExitPost sp evmSp 0 r0..r3 baseWord rest exitCond`
          where `exitCond = expResultWord r0..r3 = EvmWord.exp baseWord exponentWord`.

    Proof structure: `exp_two_mul_full_loop_boundary_of_bounded_body_spec_within`
    wraps boundary prologue/epilogue around `hLoop`. The `hLoop` hypothesis proves:
      expTwoMulLoopEntryPost → expTwoMulLoopExitPre
    in ≤ 48384 steps, which is the key semantic obligation.

    The `hLoop` proof requires the 256-iteration invariant:
    - Initial: r = 1, iterCount = 256
    - Step k: r = baseWord^(top k bits of exponentWord)
    - Final: r = EvmWord.exp baseWord exponentWord, iterCount = 0

    Each iteration applies `expFullLoopBodyNSpec` (via the peel lemma).

    This `sorry` is the only remaining obligation: proving the 256-iteration
    loop body invariant. -/
theorem expFullLoopBodySpec
    (sp evmSp cOld tOld m0 m1 m2 m3 vOld v18 : Word)
    (baseWord exponentWord : EvmWord) (rest : List EvmWord)
    (base : Word) (hbase : base &&& 1 = 0) :
    let result := EvmWord.exp baseWord exponentWord
    let r0 := result.getLimbN 0
    let r1 := result.getLimbN 1
    let r2 := result.getLimbN 2
    let r3 := result.getLimbN 3
    cpsTripleWithin expTwoMulFullLoopBoundaryBound base (base + 304)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulBoundaryPre sp evmSp cOld tOld m0 m1 m2 m3 vOld v18
        baseWord exponentWord rest)
      (expTwoMulLoopExitPost sp evmSp 0 r0 r1 r2 r3
        baseWord rest (expResultWord r0 r1 r2 r3 = result)) := by
  intro result
  let r0 := result.getLimbN 0
  let r1 := result.getLimbN 1
  let r2 := result.getLimbN 2
  let r3 := result.getLimbN 3
  -- Use the bounded-body boundary wrapper.
  -- The key obligation is `hLoop`: 256 iterations from LoopEntryPost to LoopExitPre.
  apply exp_two_mul_full_loop_boundary_of_bounded_body_spec_within
      sp evmSp cOld tOld m0 m1 m2 m3 vOld v18 0 r0 r1 r2 r3
      baseWord exponentWord rest
      (expResultWord r0 r1 r2 r3 = result) base
  -- Bound: expTwoMulFullLoopBodyBound = 48384
  · exact le_refl _
  -- hLoop: 256-iteration body proof
  -- Start: expTwoMulLoopEntryPost (r=1, iterCount=256)
  -- End: expTwoMulLoopExitPre (r=base^exp, iterCount=0)
  -- Built by 256 applications of expFullLoopBodyNSpec via the peel lemma,
  -- threading the semantic invariant at each step.
  · sorry

end EvmAsm.Evm64.Exp.Compose
