/-
  EvmAsm.Evm64.DivMod.N3CallablePublicPost

  N3 callable wrapper post-condition weakened from
  `divStackDispatchPostCallableExactFrame` to the public
  `divStackDispatchPost` via the V4 stack-post bridge.

  The result still carries the extra `memOwn (sp + signExtend12 3936)`
  atom from the callable surface — that atom needs to be subsumed into
  the public scratch ownership (or threaded as a separate ambient frame)
  for the final unconditional theorem.

  Mirrors the bzero lane's `evm_div_stack_spec_bzero_dispatchPost`
  pattern, applied to the N3 lane.
-/

import EvmAsm.Evm64.DivMod.N3CallableFromBaseEven
import EvmAsm.Evm64.DivMod.Spec.StackPostBridge

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- N3 callable wrapper weakened to public-dispatch-post (still framed
    with `memOwn (sp + signExtend12 3936)` from the callable surface). -/
theorem evm_div_callable_v4_n3_stack_pre_to_publicPost_scratch_shape_baseEven_pointedEvidence
    (sp base : Word) (a b : EvmWord)
    (v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (raVal : Word)
    (hb3z : b.getLimbN 3 = 0) (hb2nz : b.getLimbN 2 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 2)).1 ≠ 0)
    (hbase_even : base &&& (1 : Word) = 0)
    (hevidence : N3CanonicalPointedEvidence a b) :
    cpsTripleWithin (unifiedDivBound + 1) base (raVal &&& ~~~1)
      (evm_div_callable_code_v4 base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) raVal
        ((clzResult (b.getLimbN 2)).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divStackDispatchPost sp a b **
       memOwn (sp + signExtend12 3936)) :=
  cpsTripleWithin_weaken
    (fun _ hp => hp)
    (fun h hq => by
      obtain ⟨h1, h2, hd, hu, hL, hR⟩ := hq
      refine ⟨h1, h2, hd, hu, ?_, hR⟩
      exact divStackDispatchPostCallableExactFrame_weaken sp a b raVal
        (signExtend12 4095 : Word) h1 hL)
    (evm_div_callable_v4_n3_stack_pre_to_callable_post_scratch_shape_baseEven_pointedEvidence
      sp base a b
      v5 v6 v7 v10 v11Old
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem raVal
      hb3z hb2nz hshift_nz hbase_even hevidence)

end EvmAsm.Evm64
