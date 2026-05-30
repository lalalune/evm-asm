/-
  EvmAsm.Evm64.DivMod.LoopIterN2V5.IterPostV5

  v5 n=2 call-path per-digit iteration postcondition `loopIterPostN2CallV5` — the
  n=2 analog of `loopIterPostN1CallV5` (LoopIterN1.IterPostV5), over the v5 trial
  `div128Quot_v5 u2 u1 v1` (top two window limbs over the divisor's top normalized
  limb `v1`) and the full `iterWithDoubleAddback` digit result.

  Unlike the n=1 case (single-limb divisor ⇒ no borrow ⇒ skip path), the n=2 case
  has a 2-limb divisor where the trial can overshoot and the addback fires, so the
  iteration post records the full `iterWithDoubleAddback` model — exactly the
  `iterN2V5 true` digit (`iterN2V5_step`, N2V5RemainderLt).  This is the target
  the forthcoming v5 n=2 call-addback loop body produces.  Bead `evm-asm-wbc4i.9.2`.
-/

import EvmAsm.Evm64.DivMod.LoopIterN1.IterPostV5
import EvmAsm.Evm64.DivMod.Compose.FullPathN2V5Families

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- v5 n=2 call-path per-digit iteration post.  Mirror of `loopIterPostN1CallV5`
    with the n=2 divisor top limb `v1` and window top limbs `u2,u1`. -/
@[irreducible] def loopIterPostN2CallV5
    (sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem : Word) : Assertion :=
  let qHat := div128Quot_v5 u2 u1 v1
  let r := iterWithDoubleAddback qHat v0 v1 v2 v3 u0 u1 u2 u3 uTop
  let c3 := (mulsubN4 qHat v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2
  loopExitPostN2 sp j r.1 c3 r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2.1 r.2.2.2.2.2 v0 v1 v2 v3 **
  (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
  (sp + signExtend12 3960 ↦ₘ v1) **
  (sp + signExtend12 3952 ↦ₘ divKTrialCallV5DLo v1) **
  (sp + signExtend12 3944 ↦ₘ divKTrialCallV5Un0 u1) **
  (sp + signExtend12 3936 ↦ₘ divKTrialCallV5ScratchOut u2 u1 v1 scratchMem) **
  regOwn .x1

/-- The iteration post's digit result is exactly the `iterN2V5 true` schoolbook
    digit (whose correctness is proven in `N2V5RemainderLt` / `N2V5NormScaled`).
    Bridges the loop-body output to the n=2 quotient/remainder math. -/
theorem loopIterPostN2CallV5_iter_eq
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word) :
    iterWithDoubleAddback (div128Quot_v5 u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 uTop
      = iterN2V5 true v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
  unfold iterN2V5
  rw [if_pos rfl, divKTrialCallV5QHat_eq_div128Quot_v5]

end EvmAsm.Evm64
