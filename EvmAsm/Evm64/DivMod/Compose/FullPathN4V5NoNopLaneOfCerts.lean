/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN4V5NoNopLaneOfCerts

  The full n=4 v5 DIV lane combiner, in the `lane_n4` shape of
  `evm_div_stack_spec_unconditional_of_lanes_v5_div`, modulo the two runtime
  certificates.  Combines the shift≠0 and shift=0 case-split lanes by
  `by_cases (clzResult (b.getLimbN 3)).1 = 0`:

  * shift=0 → `evm_div_n4_lane_shift0_v5_of_cert` (#7626), given the shift=0
    certificate `n4Shift0LaneRuntimeCertV5`;
  * shift≠0 → `evm_div_n4_lane_shiftNz_v5_of_cert` (#7614), given the shift≠0
    certificate `n4ShiftNzLaneRuntimeCertV5`.

  Each certificate is supplied CONDITIONALLY on the shift branch (the shift=0
  cert only when `(clzResult b3).1 = 0`, the shift≠0 cert only when it is `≠ 0`),
  which is the correct shape for the eventual unconditional discharge from the
  n=4 shape.  This is the n=4 lane fully assembled end-to-end, with the ONLY
  remaining obligation being the discharge of the two certificates.  Cleaner
  variant of `evm_div_n4_lane_v5_of_cert` (#7615) now that the shift=0 lane
  (#7626) exists (so the shift=0 half is no longer a free hypothesis).
  Bead `evm-asm-wbc4i.8`.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN4V5NoNopLaneShiftNz
import EvmAsm.Evm64.DivMod.Compose.FullPathN4V5NoNopLaneShift0

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- The full v5 n=4 DIV lane: combines the shift≠0 and shift=0 case-split lanes by
    `by_cases (clzResult (b.getLimbN 3)).1 = 0`, each given its branch certificate
    conditionally.  This is the `lane_n4` obligation of
    `evm_div_stack_spec_unconditional_of_lanes_v5_div`, modulo discharging the two
    certificates `n4Shift0LaneRuntimeCertV5` / `n4ShiftNzLaneRuntimeCertV5` from the
    n=4 shape. -/
theorem evm_div_n4_lane_v5_of_certs (sp base : Word) (a b : EvmWord)
    (x1Val v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hcert0 : (clzResult (b.getLimbN 3)).1 = 0 → n4Shift0LaneRuntimeCertV5 a b)
    (hcertNz : (clzResult (b.getLimbN 3)).1 ≠ 0 → n4ShiftNzLaneRuntimeCertV5 a b) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop_v5 base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) x1Val
        ((clzResult (b.getLimbN 3)).2 >>> (63 : Nat)) v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divStackDispatchPostV5 sp a b) := by
  by_cases hsh : (clzResult (b.getLimbN 3)).1 = 0
  · exact evm_div_n4_lane_shift0_v5_of_cert sp base a b x1Val v5 v6 v7 v10 v11Old
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
      retMem dMem dloMem scratchUn0 scratchMem hb3nz hsh halign (hcert0 hsh)
  · exact evm_div_n4_lane_shiftNz_v5_of_cert sp base a b x1Val v5 v6 v7 v10 v11Old
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
      retMem dMem dloMem scratchUn0 scratchMem hb3nz hsh halign (hcertNz hsh)

end EvmAsm.Evm64
