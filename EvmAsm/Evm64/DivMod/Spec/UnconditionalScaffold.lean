/-
  EvmAsm.Evm64.DivMod.Spec.UnconditionalScaffold

  Structural 5-way `DivisorLimbCase` assembly for the unconditional DIV
  stack-spec.  Takes the four non-bzero per-lane unconditional wrappers as
  hypotheses (each a cpsTripleWithin keyed on the appropriate `NkShapeIs b`
  predicate) and produces the unconditional stack-spec by case-splitting on
  `DivisorLimbCase.elim_named`.

  The bzero lane is inlined via `evm_div_stack_spec_bzero_dispatchPost`
  (PR #7023).

  This is the assembly scaffold — the final theorem
  `evm_div_stack_spec_unconditional_of_lanes` instantiates to the public
  signature once the four lane wrappers exist (N1/N2/N3/N4).  Bead
  `evm-asm-9iqmw.7.1.7.2`.
-/

import EvmAsm.Evm64.DivMod.Spec.BzeroPublicPost
import EvmAsm.Evm64.DivMod.Spec.DivisorCasesNamedElim

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Structural 5-way DivisorLimbCase assembly: given the four per-lane
    unconditional wrappers (each at the public dispatch-post surface), this
    produces the unconditional DIV stack-spec by case-splitting on the
    divisor's shape.  The bzero case is handled internally. -/
theorem evm_div_stack_spec_unconditional_of_lanes
    (sp base : Word) (a b : EvmWord)
    (x9Val raVal v2 v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (lane_n1 : N1ShapeIs b →
      cpsTripleWithin unifiedDivBound base (base + nopOff)
        (sharedDivModCodeNoNop_v4 base)
        (divModStackDispatchPreNoX1 sp a b
          x9Val raVal v2 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratch_un0)
        (divStackDispatchPost sp a b))
    (lane_n2 : N2ShapeIs b →
      cpsTripleWithin unifiedDivBound base (base + nopOff)
        (sharedDivModCodeNoNop_v4 base)
        (divModStackDispatchPreNoX1 sp a b
          x9Val raVal v2 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratch_un0)
        (divStackDispatchPost sp a b))
    (lane_n3 : N3ShapeIs b →
      cpsTripleWithin unifiedDivBound base (base + nopOff)
        (sharedDivModCodeNoNop_v4 base)
        (divModStackDispatchPreNoX1 sp a b
          x9Val raVal v2 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratch_un0)
        (divStackDispatchPost sp a b))
    (lane_n4 : N4ShapeIs b →
      cpsTripleWithin unifiedDivBound base (base + nopOff)
        (sharedDivModCodeNoNop_v4 base)
        (divModStackDispatchPreNoX1 sp a b
          x9Val raVal v2 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratch_un0)
        (divStackDispatchPost sp a b)) :
    cpsTripleWithin unifiedDivBound base (base + nopOff)
      (sharedDivModCodeNoNop_v4 base)
      (divModStackDispatchPreNoX1 sp a b
        x9Val raVal v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (divStackDispatchPost sp a b) := by
  refine DivisorLimbCase.elim_named
    (P := fun b' => cpsTripleWithin unifiedDivBound base (base + nopOff)
      (sharedDivModCodeNoNop_v4 base)
      (divModStackDispatchPreNoX1 sp a b'
        x9Val raVal v2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (divStackDispatchPost sp a b'))
    b ?bzero ?n1 ?n2 ?n3 ?n4
  case bzero =>
    intro hbz
    exact evm_div_stack_spec_bzero_dispatchPost sp base a b
      x9Val raVal v2 v5 v6 v7 v10 v11
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratch_un0 hbz
  case n1 => exact lane_n1
  case n2 => exact lane_n2
  case n3 => exact lane_n3
  case n4 => exact lane_n4

end EvmAsm.Evm64
