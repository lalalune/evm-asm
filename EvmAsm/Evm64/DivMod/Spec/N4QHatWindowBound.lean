/-
  EvmAsm.Evm64.DivMod.Spec.N4QHatWindowBound

  The n=4 call-path trial quotient `+2` overestimate against the NORMALIZED WINDOW,
  under `U4 = 0`:
    `(n4CallAddbackBeqQHatV5 a b).toNat ≤ val256(U0..U3) / BNormVal + 2`.
  This is exactly the `hq_over` hypothesis (in `+2` form) that the generic
  double-addback bridges `mulsubN4_c3_le_two` (`c3 ≤ 2`) and
  `isAddbackCarry2Nz_of_overestimate_c3_one_of_carry_zero` (the `h_carry2` runtime
  condition `isAddbackCarry2NzN4CallV5Ab`) consume.

  Composes the original-domain `+2` (`n4CallAddbackBeqQHatV5_le_qTrue_plus_two_of_call`,
  #7573) with the window↔original bridge under `U4 = 0`
  (`n4CallAddbackBeq_window_div_eq_qTrue_of_u4_zero`, #7572).  Bead
  `evm-asm-wbc4i.8.2.2`.
-/

import EvmAsm.Evm64.DivMod.Spec.N4QHatBound
import EvmAsm.Evm64.DivMod.Spec.N4WindowDivBridge

namespace EvmAsm.Evm64

open EvmWord EvmAsm.Rv64

/-- Under `U4 = 0`, the n=4 call trial quotient overestimates the normalized-window
    quotient by at most 2 — the `+2`-form `hq_over` for the double-addback bridges. -/
theorem n4CallAddbackBeqQHatV5_le_window_div_plus_two_of_u4_zero {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hcall : isCallTrialN4 (a.getLimbN 3) (b.getLimbN 2) (b.getLimbN 3))
    (hu4 : (n4CallAddbackBeqU4 a b).toNat = 0) :
    (n4CallAddbackBeqQHatV5 a b).toNat ≤
      EvmWord.val256 (n4CallAddbackBeqU0 a b) (n4CallAddbackBeqU1 a b)
        (n4CallAddbackBeqU2 a b) (n4CallAddbackBeqU3 a b) /
      n4CallAddbackBeqBNormVal b + 2 := by
  rw [n4CallAddbackBeq_window_div_eq_qTrue_of_u4_zero hshift_nz hu4]
  exact n4CallAddbackBeqQHatV5_le_qTrue_plus_two_of_call hb3nz hshift_nz hcall

end EvmAsm.Evm64
