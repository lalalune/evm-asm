/-
  EvmAsm.Evm64.DivMod.N3CallableFromBaseEven

  N3 callable wrapper with `halign` discharged from the standard
  `base &&& 1 = 0` 2-byte alignment hypothesis.

  Mirrors `N1CallableFromBaseEven` for the n=3 lane.  Composes the
  existing `evm_div_callable_v4_n3_stack_pre_to_callable_post_scratch_shape_pointedEvidence`
  with `fullDivN1CallMaxmaxmaxExactInputAligned_of_base_even` (now valid
  for any `(base + div128CallRetOff)` alignment use, since the underlying
  fact depends only on `base &&& 1 = 0`).
-/

import EvmAsm.Evm64.DivMod.Spec.N3V4CallableExactPointedEvidence
import EvmAsm.Evm64.DivMod.HalignFromBaseEven

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- N3 DIV v4 callable wrapper that takes `base &&& 1 = 0` instead of the
    verbose halign premise. -/
theorem evm_div_callable_v4_n3_stack_pre_to_callable_post_scratch_shape_baseEven_pointedEvidence
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
      (divStackDispatchPostCallableExactFrame sp a b raVal
        (signExtend12 4095 : Word) **
       memOwn (sp + signExtend12 3936)) :=
  evm_div_callable_v4_n3_stack_pre_to_callable_post_scratch_shape_pointedEvidence
    sp base a b
    v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem raVal
    hb3z hb2nz hshift_nz
    (halign_from_base_even base hbase_even)
    hevidence

end EvmAsm.Evm64
