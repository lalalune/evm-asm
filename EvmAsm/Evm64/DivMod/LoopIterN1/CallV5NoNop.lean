/-
  EvmAsm.Evm64.DivMod.LoopIterN1.CallV5NoNop

  v5 n=1 call+skip loop-body postcondition (j = 0), the target of brick 6
  (`divK_loop_body_n1_call_skip_j0_v5_spec_within_noNop`).

  Mirror of `loopBodyN1CallSkipJ0PostV4` (LoopIterN1/Call.lean), with the trial
  quotient digit being the v5 trial `divKTrialCallV5QHat` (= `div128Quot_v5`,
  the exact floor) instead of the v4 trial.  The loop-body PRE
  (`loopBodyN1CallSkipJ0PreV4`) is version-agnostic (no `divKTrialCallV4*`
  references) and is reused directly for v5.  Bead `evm-asm-wbc4i.9.1`.
-/

import EvmAsm.Evm64.DivMod.LoopIterN1.Call
import EvmAsm.Evm64.DivMod.LoopBody.TrialCallV5

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- v5 trial scratch-cell exit value (mirror of `divKTrialCallV4ScratchOut`):
    the Phase-2a capped remainder `rhat2c`, or the prior scratch when the
    high-correction guard fired. -/
def divKTrialCallV5ScratchOut (uHi uLo vTop scratchMem : Word) : Word :=
  let rhat2c := divKTrialCallV5Rhat2c uHi uLo vTop
  if rhat2c >>> (32 : BitVec 6).toNat ≠ 0 then scratchMem else rhat2c

/-- v5 n=1 call+skip j=0 loop-body post: the digit `divKTrialCallV5QHat`
    (= exact `div128Quot_v5`) is stored, the dividend window updated by the
    no-borrow single-limb mulsub, and the div128 scratch cells settled. -/
@[irreducible]
def loopBodyN1CallSkipJ0PostV5
    (sp base v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem : Word) : Assertion :=
  let dLo := divKTrialCallV5DLo v0
  let div_un0 := divKTrialCallV5Un0 u0
  let qHat := divKTrialCallV5QHat u1 u0 v0
  loopBodyN1SkipPost sp (0 : Word) qHat v0 v1 v2 v3 u0 u1 u2 u3 uTop **
  (sp + signExtend12 3968 ↦ₘ (base + div128CallRetOff)) **
  (sp + signExtend12 3960 ↦ₘ v0) **
  (sp + signExtend12 3952 ↦ₘ dLo) **
  (sp + signExtend12 3944 ↦ₘ div_un0) **
  (sp + signExtend12 3936 ↦ₘ divKTrialCallV5ScratchOut u1 u0 v0 scratchMem) **
  regOwn .x1

end EvmAsm.Evm64
