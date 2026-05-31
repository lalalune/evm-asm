/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN4V5NoNopLane

  The full n=4 v5 DIV lane combiner (`lane_n4` shape modulo the runtime
  certificate + the shift=0 sub-lane): combines the shift≠0 and shift=0 halves
  by `by_cases (clzResult (b.getLimbN 3)).1 = 0`.  Both halves share the same
  dispatch precondition (`x9 = 4-4`, `x2 = (clzResult (b.getLimbN 3)).2 >>> 63`)
  and post (`divStackDispatchPostV5`).  The shift=0 half is taken as a hypothesis
  `shift0lane` (its v5 code path is not yet built), and the shift≠0 half is
  discharged by the borrow case-split lane `evm_div_n4_lane_shiftNz_v5_of_cert`
  (#7614) given the runtime certificate.  v5 mirror of `evm_div_n2_lane_v5`
  (FullPathN2V5Lane), with `N4ShapeIs` (just `b3 ≠ 0`) in place of the n=2 shape.
  Bead `evm-asm-wbc4i.8`.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN4V5NoNopLaneShiftNz

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- The full v5 n=4 DIV lane: combines the shift≠0 and shift=0 halves by
    `by_cases (clzResult (b.getLimbN 3)).1 = 0`.  The shift=0 half is supplied as
    a hypothesis `shift0lane`; the shift≠0 half is the borrow case-split lane
    given the runtime certificate `n4ShiftNzLaneRuntimeCertV5`.  This is the
    `lane_n4` obligation of `evm_div_stack_spec_unconditional_of_lanes_v5_div`,
    modulo discharging `shift0lane` and the certificate. -/
theorem evm_div_n4_lane_v5_of_cert (sp base : Word) (a b : EvmWord)
    (x1Val v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (shift0lane : (clzResult (b.getLimbN 3)).1 = 0 →
      cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop_v5 base)
        (divModStackDispatchPreNoX1 sp a b
          (signExtend12 (4 : BitVec 12) - (4 : Word)) x1Val
          ((clzResult (b.getLimbN 3)).2 >>> (63 : Nat)) v5 v6 v7 v10 v11Old
          q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
         ((sp + signExtend12 3936) ↦ₘ scratchMem))
        (divStackDispatchPostV5 sp a b))
    (hcert : n4ShiftNzLaneRuntimeCertV5 a b) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop_v5 base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) x1Val
        ((clzResult (b.getLimbN 3)).2 >>> (63 : Nat)) v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divStackDispatchPostV5 sp a b) := by
  by_cases hsh : (clzResult (b.getLimbN 3)).1 = 0
  · exact shift0lane hsh
  · exact evm_div_n4_lane_shiftNz_v5_of_cert sp base a b x1Val v5 v6 v7 v10 v11Old
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
      retMem dMem dloMem scratchUn0 scratchMem hb3nz hsh halign hcert

end EvmAsm.Evm64
