/-
  EvmAsm.Evm64.DivMod.Spec.N3V4CallableExactSelectedEvidenceCanonical

  Callable-shape wrapper for the N3 DIV v4 route that consumes
  `fullDivN3SelectedCarryV4` and the `mulsub ∧ overestimate` conjunction
  **at the canonical bltu pair** directly, internally producing
  `N3CallableSelectedShapeEvidence` via `.of_canonical` and delegating to
  `evm_div_callable_v4_n3_stack_pre_to_callable_post_scratch_shape_selectedEvidence`.

  Mirrors `N2V4CallableExactSelectedEvidenceCanonical` for the n=3 lane.
-/

import EvmAsm.Evm64.DivMod.CallableV4DivShape
import EvmAsm.Evm64.DivMod.Spec.N3CallableSelectedShapeEvidenceCanonical

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- N3 DIV v4 callable wrapper consuming pointed canonical-bltu evidence
    (selected carry plus mulsub ∧ overestimate at the canonical pair).
    Internally builds the `N3CallableSelectedShapeEvidence` bundle and
    delegates to the existing `_selectedEvidence` wrapper. -/
theorem evm_div_callable_v4_n3_stack_pre_to_callable_post_scratch_shape_canonicalEvidence
    (sp base : Word) (a b : EvmWord)
    (v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (raVal : Word)
    (hb3z : b.getLimbN 3 = 0) (hb2nz : b.getLimbN 2 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 2)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hcarry : fullDivN3SelectedCarryV4
      (n3V4CanonicalBltu1 a b) (n3V4CanonicalBltu0 a b)
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3))
    (harith : fullDivN3MulSubEqV4
        (n3V4CanonicalBltu1 a b) (n3V4CanonicalBltu0 a b)
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      fullDivN3QuotientOverestimateV4
        (n3V4CanonicalBltu1 a b) (n3V4CanonicalBltu0 a b)
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) :
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
  evm_div_callable_v4_n3_stack_pre_to_callable_post_scratch_shape_selectedEvidence
    sp base a b
    v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem raVal
    hb3z hb2nz hshift_nz halign
    (N3CallableSelectedShapeEvidence.of_canonical hcarry harith)

end EvmAsm.Evm64
