/-
  EvmAsm.Evm64.DivMod.Spec.UnconditionalCanonicalFramed

  Framed variant of `evm_div_stack_spec_unconditional_canonical_of_lanes`
  (UnconditionalCanonical.lean / PR #7029): adds the
  `(sp + signExtend12 3936) ↦ₘ scratchMem` cell to the precondition and
  `memOwn (sp + signExtend12 3936)` to the postcondition.

  This shape matches the framing artifact carried by the callable→public-
  dispatch-post bridges (`N{1,2,3}CallablePublicPost`, PRs #7050/#7049/#7047)
  and the framed bzero wrapper (`BzeroPublicPostFramed`, PR #7051): once the
  dispatch-surface lane wrappers exist at the framed shape, instantiation
  gives the final unconditional public theorem with `memOwn 3936` threaded
  ambiently on both sides.
-/

import EvmAsm.Evm64.DivMod.Spec.DivisorCasesNamedElim
import EvmAsm.Evm64.DivMod.BzeroPublicPostFramed

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Framed 5-way DivisorLimbCase assembly at the public `divCode` /
    `divStackDispatchPost` surface, threading `(sp + 3936) ↦ₘ scratchMem` on
    the pre and `memOwn (sp + 3936)` on the post.

    Bzero case is handled internally via
    `evm_div_bzero_stack_spec_within_dispatch_publicPost_framed`
    (PR #7051).  The four lane hypotheses take the same framed form
    (`((sp+3936) ↦ₘ scratchMem)` on pre, `memOwn (sp+3936)` on post),
    keyed on `NkShapeIs b`. -/
theorem evm_div_stack_spec_unconditional_canonical_framed_of_lanes
    (sp base : Word) (a b : EvmWord)
    (x9 x2 v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (scratchMem : Word)
    (lane_n1 : N1ShapeIs b →
      cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode base)
        (divModStackDispatchPre sp a b
          x9 x2 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratch_un0 **
         ((sp + signExtend12 3936) ↦ₘ scratchMem))
        (divStackDispatchPost sp a b **
         memOwn (sp + signExtend12 3936)))
    (lane_n2 : N2ShapeIs b →
      cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode base)
        (divModStackDispatchPre sp a b
          x9 x2 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratch_un0 **
         ((sp + signExtend12 3936) ↦ₘ scratchMem))
        (divStackDispatchPost sp a b **
         memOwn (sp + signExtend12 3936)))
    (lane_n3 : N3ShapeIs b →
      cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode base)
        (divModStackDispatchPre sp a b
          x9 x2 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratch_un0 **
         ((sp + signExtend12 3936) ↦ₘ scratchMem))
        (divStackDispatchPost sp a b **
         memOwn (sp + signExtend12 3936)))
    (lane_n4 : N4ShapeIs b →
      cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode base)
        (divModStackDispatchPre sp a b
          x9 x2 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratch_un0 **
         ((sp + signExtend12 3936) ↦ₘ scratchMem))
        (divStackDispatchPost sp a b **
         memOwn (sp + signExtend12 3936))) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode base)
      (divModStackDispatchPre sp a b
        x9 x2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divStackDispatchPost sp a b **
       memOwn (sp + signExtend12 3936)) := by
  refine DivisorLimbCase.elim_named
    (P := fun b' => cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode base)
      (divModStackDispatchPre sp a b'
        x9 x2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divStackDispatchPost sp a b' **
       memOwn (sp + signExtend12 3936)))
    b ?bzero ?n1 ?n2 ?n3 ?n4
  case bzero =>
    intro hbz
    exact evm_div_bzero_stack_spec_within_dispatch_publicPost_framed sp base a b
      x9 x2 v5 v6 v7 v10 v11
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratch_un0 scratchMem hbz
  case n1 => exact lane_n1
  case n2 => exact lane_n2
  case n3 => exact lane_n3
  case n4 => exact lane_n4

end EvmAsm.Evm64
