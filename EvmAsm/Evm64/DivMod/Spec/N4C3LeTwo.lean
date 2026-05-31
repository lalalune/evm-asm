/-
  EvmAsm.Evm64.DivMod.Spec.N4C3LeTwo

  The n=4 call-path mulsub borrow `c3 ≤ 2` under `U4 = 0` (bead `.8.2.2.4`): with
  the `+2` overestimate over the normalized window (#7574) and the normalized
  divisor's nonzero `OR`, the generic `mulsubN4_c3_le_two` gives the mulsub carry-out
  `c3` of the n=4 call-path trial at most 2.  This is the `c3 ≤ 2` the double-addback
  (carry2) branch handles.  Bead `evm-asm-wbc4i.8.2.2.4`.
-/

import EvmAsm.Evm64.DivMod.Spec.N4QHatWindowBound
import EvmAsm.Evm64.EvmWordArith.DivMulsubC3LeTwo

namespace EvmAsm.Evm64

open EvmWord EvmAsm.Rv64

/-- Under `U4 = 0`, the n=4 call-path mulsub carry-out `c3` is at most 2. -/
theorem n4CallAddbackBeq_mulsub_c3_le_two_of_u4_zero {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hcall : isCallTrialN4 (a.getLimbN 3) (b.getLimbN 2) (b.getLimbN 3))
    (hu4 : (n4CallAddbackBeqU4 a b).toNat = 0) :
    (mulsubN4 (n4CallAddbackBeqQHatV5 a b)
        (n4CallAddbackBeqB0Prime b) (n4CallAddbackBeqB1Prime b)
        (n4CallAddbackBeqB2Prime b) (n4CallAddbackBeqB3Prime b)
        (n4CallAddbackBeqU0 a b) (n4CallAddbackBeqU1 a b)
        (n4CallAddbackBeqU2 a b) (n4CallAddbackBeqU3 a b)).2.2.2.2.toNat ≤ 2 :=
  mulsubN4_c3_le_two
    (n4CallAddbackBeqNormalizedDivisor_ne_zero hb3nz)
    (n4CallAddbackBeqQHatV5_le_window_div_plus_two_of_u4_zero hb3nz hshift_nz hcall hu4)

end EvmAsm.Evm64
