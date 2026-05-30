/-
  EvmAsm.Evm64.DivMod.LoopIterN1.IterPostDispatchV5

  The v5 n=1 per-digit iteration post *dispatcher* `loopIterPostN1V5` (mirror of
  `loopIterPostN1`, LoopDefs/Post.lean) selecting the call vs max iteration post
  by the digit's `bltu` flag, with the iteration-ready bodies (#7270/#7272)
  re-stated against it.  The building block over which the v5 n=1 4-digit loop
  composition (iter10 → iter210 → unified) dispatches.  Bead `evm-asm-wbc4i.9.1`.
-/

import EvmAsm.Evm64.DivMod.LoopIterN1.IterBodyV5
import EvmAsm.Evm64.DivMod.LoopIterN1.IterBodyMaxV5

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- v5 n=1 per-digit iteration post, dispatched on the call/max branch.  Mirror
    of `loopIterPostN1`. -/
def loopIterPostN1V5 (bltu : Bool)
    (sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem : Word) : Assertion :=
  match bltu with
  | true  => loopIterPostN1CallV5 sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem
  | false => loopIterPostN1Max sp j v0 v1 v2 v3 u0 u1 u2 u3 uTop ** empAssertion

@[simp] theorem loopIterPostN1V5_true
    {sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem : Word} :
    loopIterPostN1V5 true sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem =
    loopIterPostN1CallV5 sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem := rfl

@[simp] theorem loopIterPostN1V5_false
    {sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem : Word} :
    loopIterPostN1V5 false sp base j v0 v1 v2 v3 u0 u1 u2 u3 uTop scratchMem =
    (loopIterPostN1Max sp j v0 v1 v2 v3 u0 u1 u2 u3 uTop ** empAssertion) := rfl

end EvmAsm.Evm64
