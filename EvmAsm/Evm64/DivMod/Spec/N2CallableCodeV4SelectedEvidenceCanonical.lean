/-
  EvmAsm.Evm64.DivMod.Spec.N2CallableCodeV4SelectedEvidenceCanonical

  Callable-shape wrapper for the N2 DIV v4 route over `evm_div_callable_code_v4`
  that consumes `fullDivN2SelectedCarryV4` and the `mulsub ∧ overestimate`
  conjunction **at the canonical bltu triple** directly, internally producing
  `N2CallableSelectedShapeEvidence` via `.of_canonical` and delegating to
  `evm_div_callable_v4_n2_stack_pre_to_callable_post_scratch_shape_selectedEvidence`
  in `CallableV4DivShape`.

  This mirrors `N3V4CallableExactSelectedEvidenceCanonical` for the n=2 lane
  over the callable_code form. (The n=2 wrappers over `divCode_v4` /
  `divCode_noNop_v4` are provided by `N2V4CallableExactSelectedEvidenceCanonical`.)
-/

import EvmAsm.Evm64.DivMod.CallableV4DivShape
import EvmAsm.Evm64.DivMod.Spec.N2CallableSelectedShapeEvidenceCanonical

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- N2 DIV v4 `evm_div_callable_code_v4` wrapper consuming pointed
    canonical-bltu evidence (selected carry plus mulsub ∧ overestimate at
    the canonical triple). Internally builds the
    `N2CallableSelectedShapeEvidence` bundle and delegates to the existing
    `_selectedEvidence` wrapper. -/
theorem evm_div_callable_v4_n2_stack_pre_to_callable_post_scratch_shape_canonicalEvidence
    (sp base : Word) (a b : EvmWord)
    (v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (raVal : Word)
    (hb3z : b.getLimbN 3 = 0) (hb2z : b.getLimbN 2 = 0)
    (hb1nz : b.getLimbN 1 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 1)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hcarry : fullDivN2SelectedCarryV4
      (n2V4CanonicalBltu2 a b) (n2V4CanonicalBltu1 a b) (n2V4CanonicalBltu0 a b)
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3))
    (harith : fullDivN2MulSubEqV4
        (n2V4CanonicalBltu2 a b) (n2V4CanonicalBltu1 a b) (n2V4CanonicalBltu0 a b)
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      fullDivN2QuotientOverestimateV4
        (n2V4CanonicalBltu2 a b) (n2V4CanonicalBltu1 a b) (n2V4CanonicalBltu0 a b)
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) :
    cpsTripleWithin (unifiedDivBound + 1) base (raVal &&& ~~~1)
      (evm_div_callable_code_v4 base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) raVal
        ((clzResult (b.getLimbN 1)).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divStackDispatchPostCallableExactFrame sp a b raVal
        (signExtend12 4095 : Word) **
       memOwn (sp + signExtend12 3936)) :=
  evm_div_callable_v4_n2_stack_pre_to_callable_post_scratch_shape_selectedEvidence
    sp base a b
    v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem raVal
    hb3z hb2z hb1nz hshift_nz halign
    (N2CallableSelectedShapeEvidence.of_canonical hcarry harith)

end EvmAsm.Evm64
