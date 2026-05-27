/-
  EvmAsm.Evm64.DivMod.N1CallablePublicPost

  N1 callable wrapper post-condition weakened to public `divStackDispatchPost`
  via the V4 stack-post bridge.

  Mirrors `N{2,3}CallablePublicPost` for the n=1 if-borrow lane.
-/

import EvmAsm.Evm64.DivMod.N1CallableFromBaseEven
import EvmAsm.Evm64.DivMod.Spec.StackPostBridge

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- N1 callable wrapper weakened to public-dispatch-post. -/
theorem evm_div_callable_v4_n1_stack_pre_to_publicPost_scratch_shape_baseEven_selectedIfBorrowWordEvidence
    (sp base : Word) (a b : EvmWord)
    (v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (raVal : Word)
    (hbnz : b ≠ 0)
    (hb3z : b.getLimbN 3 = 0) (hb2z : b.getLimbN 2 = 0)
    (hb1z : b.getLimbN 1 = 0)
    (hshift_nz : (clzResult (b.getLimbN 0)).1 ≠ 0)
    (hbase_even : base &&& (1 : Word) = 0)
    (hevidence : N1CallableSelectedIfBorrowWordEvidence a b) :
    cpsTripleWithin (unifiedDivBound + 1) base (raVal &&& ~~~1)
      (evm_div_callable_code_v4 base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) raVal
        ((clzResult (b.getLimbN 0)).2 >>> (63 : Nat))
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
    (evm_div_callable_v4_n1_stack_pre_to_callable_post_scratch_shape_baseEven_selectedIfBorrowWordEvidence
      sp base a b
      v5 v6 v7 v10 v11Old
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem raVal
      hbnz hb3z hb2z hb1z hshift_nz hbase_even hevidence)

end EvmAsm.Evm64
