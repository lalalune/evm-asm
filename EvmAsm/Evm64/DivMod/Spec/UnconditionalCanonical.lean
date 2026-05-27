/-
  EvmAsm.Evm64.DivMod.Spec.UnconditionalCanonical

  Canonical 5-way `DivisorLimbCase` assembly for the unconditional DIV
  stack-spec at the public `divCode` / `divStackDispatchPost` surface
  matching the legacy branch-certificate form `evm_div_stack_spec`.

  Takes the four non-bzero per-lane unconditional wrappers as hypotheses
  (each at the same `divCode` / `divStackDispatchPost` surface, keyed on
  `NkShapeIs b`) and handles the bzero case internally.  Once the four
  lane wrappers are proven from shape alone, instantiation gives the
  final public `evm_div_stack_spec_unconditional` theorem.

  Mirrors `UnconditionalScaffold` for the dispatch surface used by
  `evm_div_stack_spec` (the branch-certificate-driven version) — that is,
  uses `divCode base` (not `sharedDivModCodeNoNop_v4`), making the
  resulting theorem a drop-in replacement at the dispatcher surface.
-/

import EvmAsm.Evm64.DivMod.Spec.Unified
import EvmAsm.Evm64.DivMod.Spec.DivisorCasesNamedElim

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Canonical 5-way DivisorLimbCase assembly at the public `divCode` /
    `divStackDispatchPost` surface.  Takes four per-lane wrappers at the
    same surface keyed on `NkShapeIs b`; handles the bzero case via
    `evm_div_bzero_stack_spec_within_dispatch_uni`.

    The state variables `x9 x2 v5 v6 v7 v10 v11 q0..u7 nMem..scratch_un0`
    are universally quantified, matching the shape of `evm_div_stack_spec`
    except that the `branch : DivStackSpecCase ...` premise is replaced
    by the four lane hypotheses.  Once those four are proven from shape,
    instantiation gives an unconditional theorem with no premise about
    `b` other than what each `NkShapeIs` predicate captures internally. -/
theorem evm_div_stack_spec_unconditional_canonical_of_lanes
    (sp base : Word) (a b : EvmWord)
    (x9 x2 v5 v6 v7 v10 v11 : Word)
    (q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratch_un0 : Word)
    (lane_n1 : N1ShapeIs b →
      cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode base)
        (divModStackDispatchPre sp a b
          x9 x2 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratch_un0)
        (divStackDispatchPost sp a b))
    (lane_n2 : N2ShapeIs b →
      cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode base)
        (divModStackDispatchPre sp a b
          x9 x2 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratch_un0)
        (divStackDispatchPost sp a b))
    (lane_n3 : N3ShapeIs b →
      cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode base)
        (divModStackDispatchPre sp a b
          x9 x2 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratch_un0)
        (divStackDispatchPost sp a b))
    (lane_n4 : N4ShapeIs b →
      cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode base)
        (divModStackDispatchPre sp a b
          x9 x2 v5 v6 v7 v10 v11
          q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratch_un0)
        (divStackDispatchPost sp a b)) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode base)
      (divModStackDispatchPre sp a b
        x9 x2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (divStackDispatchPost sp a b) := by
  refine DivisorLimbCase.elim_named
    (P := fun b' => cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode base)
      (divModStackDispatchPre sp a b'
        x9 x2 v5 v6 v7 v10 v11
        q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0)
      (divStackDispatchPost sp a b'))
    b ?bzero ?n1 ?n2 ?n3 ?n4
  case bzero =>
    intro hbz
    exact evm_div_bzero_stack_spec_within_dispatch_uni sp base a b
      x9 x2 v5 v6 v7 v10 v11
      q0 q1 q2 q3 u0 u1 u2 u3 u4 u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratch_un0 hbz
  case n1 => exact lane_n1
  case n2 => exact lane_n2
  case n3 => exact lane_n3
  case n4 => exact lane_n4

end EvmAsm.Evm64
