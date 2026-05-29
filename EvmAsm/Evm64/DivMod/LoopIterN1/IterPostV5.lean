/-
  EvmAsm.Evm64.DivMod.LoopIterN1.IterPostV5

  v5 n=1 call-path per-digit iteration postcondition `loopIterPostN1CallV5`
  (mirror of `loopIterPostN1CallV4NoX1`, LoopDefs/Post.lean, but over the EXACT
  v5 trial `div128Quot_v5` and the clean named scratch defs).  Plus the skip
  bridges connecting the v5 loop-body posts (#7266/#7267) to this iteration post.

  Because `div128Quot_v5` is the exact floor, the single-limb mulsub never
  borrows, so the loop body always takes the SKIP path — the `iterWithDoubleAddback`
  model reduces to the skip mulsub (the addback is a no-op).  These bridges feed
  the v5 n=1 loop iteration (no `Carry2NzAll`).  Bead `evm-asm-wbc4i.9.1`.
-/

import EvmAsm.Evm64.DivMod.LoopIterN1.CallSkipJgt0V5
import EvmAsm.Evm64.DivMod.Spec.N1V5CodeQuotNoBorrow

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- v5 n=1 call-path per-digit iteration post: the schoolbook digit result
    (`iterWithDoubleAddback` over `div128Quot_v5`) with the div128 scratch cells
    settled (via the named v5 scratch defs).  Mirror of `loopIterPostN1CallV4NoX1`
    plus `regOwn .x1`. -/
@[irreducible] def loopIterPostN1CallV5
    (sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem : Word) : Assertion :=
  let qHat := div128Quot_v5 u1 u0 v0
  let r := iterWithDoubleAddback qHat v0 v1 v2 v3 u0 u1 u2 u3 uTop
  let c3 := (mulsubN4 qHat v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2
  loopExitPostN1 sp j r.1 c3 r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2.1 r.2.2.2.2.2 v0 v1 v2 v3 **
  (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
  (sp + signExtend12 3960 ↦ₘ v0) **
  (sp + signExtend12 3952 ↦ₘ divKTrialCallV5DLo v0) **
  (sp + signExtend12 3944 ↦ₘ divKTrialCallV5Un0 u0) **
  (sp + signExtend12 3936 ↦ₘ divKTrialCallV5ScratchOut u1 u0 v0 scratchMem) **
  regOwn .x1

/-- Skip bridge (j=0): the v5 j=0 loop-body post equals the iteration post when
    the mulsub does not borrow (which, for the exact v5 trial, always holds). -/
theorem loopIterPostN1CallV5_j0_skip
    {sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem : Word}
    (hb : ¬BitVec.ult uTop
      (mulsubN4_c3 (div128Quot_v5 u1 u0 v0) v0 v1 v2 v3 u0 u1 u2 u3)) :
    loopBodyN1CallSkipJ0PostV5 sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem =
    loopIterPostN1CallV5 sp base (0 : Word) v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem := by
  unfold loopBodyN1CallSkipJ0PostV5 loopIterPostN1CallV5
  rw [divKTrialCallV5QHat_eq_div128Quot_v5]
  delta loopBodyN1SkipPost loopBodySkipPost loopExitPostN1 loopExitPost
    iterWithDoubleAddback
  unfold mulsubN4_c3 at hb
  simp only [if_neg hb]

/-- Skip bridge (j>0): the v5 steady-state loop-body post equals the iteration
    post when the mulsub does not borrow. -/
theorem loopIterPostN1CallV5_jgt0_skip
    {sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem : Word}
    (hb : ¬BitVec.ult uTop
      (mulsubN4_c3 (div128Quot_v5 u1 u0 v0) v0 v1 v2 v3 u0 u1 u2 u3)) :
    loopBodyN1CallSkipJgt0PostV5 sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem =
    loopIterPostN1CallV5 sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem := by
  unfold loopBodyN1CallSkipJgt0PostV5 loopIterPostN1CallV5
  rw [divKTrialCallV5QHat_eq_div128Quot_v5]
  delta loopBodyN1SkipPost loopBodySkipPost loopExitPostN1 loopExitPost
    iterWithDoubleAddback
  unfold mulsubN4_c3 at hb
  simp only [if_neg hb]

end EvmAsm.Evm64
