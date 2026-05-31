/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN1N2V5StackSpecUnconditional

  The n=1 and n=2 v5 DIV lanes in the canonical shape-predicate (`N1ShapeIs` /
  `N2ShapeIs`) form, matching the n=3 `evm_div_n3_stack_spec_unconditional`
  (FullPathN3V5StackSpecUnconditional).  Repackages the complete lanes
  `evm_div_n1_lane_v5` / `evm_div_n2_lane_complete_v5` — which take the raw shape
  facts — under the named shape predicates, so all of n1/n2/n3 are available in the
  uniform scaffold-ready form (`UnconditionalScaffoldV5Div` `lane_n1`/`lane_n2`
  hooks, modulo the assembly's `v2` reconciliation).  Bead `evm-asm-wbc4i.9.x`.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN1V5LaneShift0
import EvmAsm.Evm64.DivMod.Compose.FullPathN2V5LaneShift0
import EvmAsm.Evm64.DivMod.Spec.DivisorShapeNamed

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- The complete v5 n=1 DIV lane, under the named `N1ShapeIs` predicate. -/
theorem evm_div_n1_stack_spec_unconditional (sp base : Word) (a b : EvmWord)
    (raVal v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem : Word)
    (retMem dMem dloMem scratch_un0 scratchMem : Word)
    (hshape : N1ShapeIs b)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop_v5 base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) raVal
        ((clzResult (b.getLimbN 0)).2 >>> (63 : Nat)) v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divStackDispatchPostV5 sp a b) := by
  have hbnz : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0 := by
    intro heq
    exact hshape.2.2.2.2
      (BitVec.or_eq_zero_iff.mp
        (BitVec.or_eq_zero_iff.mp
          (BitVec.or_eq_zero_iff.mp heq).1).1).1
  exact evm_div_n1_lane_v5 sp base a b raVal v5 v6 v7 v10 v11Old
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
    retMem dMem dloMem scratch_un0 scratchMem rfl rfl rfl rfl rfl rfl rfl rfl
    hbnz hshape.2.1 hshape.2.2.1 hshape.2.2.2.1 halign

/-- The complete v5 n=2 DIV lane, under the named `N2ShapeIs` predicate. -/
theorem evm_div_n2_stack_spec_unconditional (sp base : Word) (a b : EvmWord)
    (raVal v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem : Word)
    (retMem dMem dloMem scratch_un0 scratchMem : Word)
    (hshape : N2ShapeIs b)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop_v5 base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) raVal
        ((clzResult (b.getLimbN 1)).2 >>> (63 : Nat)) v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratch_un0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divStackDispatchPostV5 sp a b) :=
  evm_div_n2_lane_complete_v5 sp base a b raVal v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
    retMem dMem dloMem scratch_un0 scratchMem
    hshape.1 hshape.2.1 hshape.2.2.1 hshape.2.2.2 halign

end EvmAsm.Evm64
