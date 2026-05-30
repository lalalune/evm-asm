/-
  EvmAsm.Evm64.DivMod.LoopIterN1.CallAddbackV5NoNop

  v5 call+ADDBACK loop-body postconditions over `sharedDivModCodeNoNop_v5`.

  The n=1 v5 loop uses the no-borrow SKIP path (`CallSkipJ0V5`), but the n≥2 loops
  take the ADDBACK path when the multi-limb trial overshoots.  These are the
  postcondition defs the (forthcoming) v5 call-addback loop body produces —
  mirrors of `loopBodyN1CallAddbackBeqJ0PostV4` (CallAddbackV4NoNop) with the v5
  trial scratch defs (`divKTrialCallV5DLo`/`Un0`/`QHat`/`ScratchOut`).  The body
  PRE (`loopBodyN1CallSkipJ0PreV4`) and the shared addback-state post
  (`loopBodyN1AddbackBeqPost`) are version-agnostic and reused directly.

  The body proof composes `divK_trial_call_full_v5_named` (TrialCallFullV5Named) +
  `divK_mulsub_correction_addback_beq_v5` (MulsubCorrectionAddbackV5NoNop) +
  `divK_store_loop_j0_v5` (StoreLoopV5) — exactly mirroring the v5 skip body
  `CallSkipJ0V5` with the addback brick in place of the skip brick.  Bead
  `evm-asm-wbc4i.9.2`.
-/

import EvmAsm.Evm64.DivMod.LoopIterN1.CallV5NoNop
import EvmAsm.Evm64.DivMod.LoopIterN1.CallAddbackV4NoNop

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- v5 call+addback j=0 loop-body post (with `regOwn .x1`).  Mirror of
    `loopBodyN1CallAddbackBeqJ0PostV4` with the v5 trial scratch defs. -/
@[irreducible]
def loopBodyN1CallAddbackBeqJ0PostV5
    (sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem : Word) : Assertion :=
  let dLo := divKTrialCallV5DLo v0
  let div_un0 := divKTrialCallV5Un0 u0
  let qHat := divKTrialCallV5QHat u1 u0 v0
  let scratchOut := divKTrialCallV5ScratchOut u1 u0 v0 scratchMem
  loopBodyN1AddbackBeqPost sp (0 : Word) qHat v0 v1 v2 v3 u0 u1 u2 u3 uTop **
  (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
  (sp + signExtend12 3960 ↦ₘ v0) **
  (sp + signExtend12 3952 ↦ₘ dLo) **
  (sp + signExtend12 3944 ↦ₘ div_un0) **
  (sp + signExtend12 3936 ↦ₘ scratchOut) **
  regOwn .x1

/-- v5 call+addback j=0 loop-body post without `regOwn .x1` (for the
    exact-`x1`-preserving variant). -/
@[irreducible]
def loopBodyN1CallAddbackBeqJ0PostV5NoX1
    (sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem : Word) : Assertion :=
  let dLo := divKTrialCallV5DLo v0
  let div_un0 := divKTrialCallV5Un0 u0
  let qHat := divKTrialCallV5QHat u1 u0 v0
  let scratchOut := divKTrialCallV5ScratchOut u1 u0 v0 scratchMem
  loopBodyN1AddbackBeqPost sp (0 : Word) qHat v0 v1 v2 v3 u0 u1 u2 u3 uTop **
  (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
  (sp + signExtend12 3960 ↦ₘ v0) **
  (sp + signExtend12 3952 ↦ₘ dLo) **
  (sp + signExtend12 3944 ↦ₘ div_un0) **
  (sp + signExtend12 3936 ↦ₘ scratchOut)

end EvmAsm.Evm64
