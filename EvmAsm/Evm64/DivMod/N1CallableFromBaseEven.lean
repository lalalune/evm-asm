/-
  EvmAsm.Evm64.DivMod.N1CallableFromBaseEven

  N1 callable wrapper with `halign` discharged from the standard
  `base &&& 1 = 0` 2-byte alignment hypothesis.

  Eliminates one of the two non-shape premises in
  `evm_div_callable_v4_n1_stack_pre_to_callable_post_scratch_shape_selectedIfBorrowWordEvidence_inputHdivRoute`.
  The remaining premise is `N1CallableSelectedIfBorrowWordEvidence`, which
  is the pointed evidence package the named c3 invariant work will
  ultimately discharge.
-/

import EvmAsm.Evm64.DivMod.CallableV4DivShape
import EvmAsm.Evm64.DivMod.HalignFromBaseEven

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- N1 callable wrapper taking `base &&& 1 = 0` instead of the explicit
    halign premise. Internally discharges halign via
    `fullDivN1CallMaxmaxmaxExactInputAligned_of_base_even`. -/
theorem evm_div_callable_v4_n1_stack_pre_to_callable_post_scratch_shape_baseEven_selectedIfBorrowWordEvidence
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
      (divStackDispatchPostCallableExactFrame sp a b raVal
        (signExtend12 4095 : Word) **
       memOwn (sp + signExtend12 3936)) :=
  evm_div_callable_v4_n1_stack_pre_to_callable_post_scratch_shape_selectedIfBorrowWordEvidence_inputHdivRoute
    sp base a b v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem raVal
    hbnz hb3z hb2z hb1z hshift_nz
    (fullDivN1CallMaxmaxmaxExactInputAligned_of_base_even sp base
      jMem (1 : Word) (fullDivN1Shift (b.getLimbN 0))
      (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
        (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).1
      (a.getLimbN 0 >>> ((fullDivN1AntiShift (b.getLimbN 0)).toNat % 64))
      v11Old (fullDivN1AntiShift (b.getLimbN 0))
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      (0 : Word) (0 : Word) (0 : Word) (0 : Word)
      retMem dMem dloMem scratchUn0 scratchMem raVal hbase_even)
    hevidence

end EvmAsm.Evm64
