/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN4V5NoNopLaneOfShiftNzCert

  The full n=4 v5 DIV lane in the `lane_n4` shape, with the shift=0 runtime
  certificate DISCHARGED FROM SHAPE — so the ONLY remaining obligation is the
  shift≠0 certificate.  Instantiates `evm_div_n4_lane_v5_of_certs` (#7628), whose
  `hcert0` (the shift=0 cert) is supplied unconditionally by
  `evm_div_n4_shift0_cert_of_shape` (#7635) and whose `hcertNz` (the shift≠0 cert)
  is carried as a hypothesis.  This is `lane_n4` modulo the single deep Knuth-D
  no-wrap discharge of `n4ShiftNzLaneRuntimeCertV5`.  Bead `evm-asm-wbc4i.8`.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN4V5NoNopLaneOfCerts
import EvmAsm.Evm64.DivMod.Spec.N4V5Shift0CertOfShape

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- n=4 v5 DIV lane (`lane_n4` shape) with the shift=0 certificate discharged from
    the shape; takes only the shift≠0 certificate `n4ShiftNzLaneRuntimeCertV5`
    (conditionally on `shift ≠ 0`). -/
theorem evm_div_n4_lane_v5_of_shiftNz_cert (sp base : Word) (a b : EvmWord)
    (x1Val v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hcertNz : (clzResult (b.getLimbN 3)).1 ≠ 0 → n4ShiftNzLaneRuntimeCertV5 a b) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_noNop_v5 base)
      (divModStackDispatchPreNoX1 sp a b
        (signExtend12 (4 : BitVec 12) - (4 : Word)) x1Val
        ((clzResult (b.getLimbN 3)).2 >>> (63 : Nat)) v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divStackDispatchPostV5 sp a b) :=
  evm_div_n4_lane_v5_of_certs sp base a b x1Val v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem jMem
    retMem dMem dloMem scratchUn0 scratchMem hb3nz halign
    (fun hsh => evm_div_n4_shift0_cert_of_shape a b hb3nz hsh)
    hcertNz

end EvmAsm.Evm64
