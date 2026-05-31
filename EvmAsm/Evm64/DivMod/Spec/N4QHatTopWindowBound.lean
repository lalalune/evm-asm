/-
  EvmAsm.Evm64.DivMod.Spec.N4QHatTopWindowBound

  The n=4 v5 call trial quotient overestimates the NORMALIZED TOP-WINDOW quotient
  `(U4·2^64 + U3) / B3'` by at most 1 — UNCONDITIONALLY on the call path (needs
  only `b3 ≠ 0` and the call-trial condition `isCallTrialN4`, NO `U4 = 0`):

    `qHatV5 ≤ (U4·2^64 + U3) / B3' + 1`.

  This is bead `evm-asm-wbc4i.8.2.2.1` (the top-limb `+1` bound).  It is the V5
  counterpart of the V4 `n4CallAddbackBeqQHatV4_le_128_div_plus_one_of_*`, but is
  STRICTLY SIMPLER: the V5 trial upper bound `div128Quot_v5_le_q_true_plus_one`
  (V5.4.5) is itself unconditional, so none of the V4 `rhatdd_hi_zero` / `Un21`
  side-premises are required.

  Unlike `n4CallAddbackBeqQHatV5_le_window_div_plus_one_of_u4_zero` (N4QHatLeOne),
  which targets the `val256`-of-low-four-limbs quotient and only holds under
  `U4 = 0` (where `qHat ≤ 1`), this top-window form holds for `U4 = 1` too — the
  foundation for the `U4 > 0` double-addback (`+2`) overestimate (`.8.2.2.3`).
  Bead `evm-asm-wbc4i.8.2.2.1`.
-/

import EvmAsm.Evm64.DivMod.Spec.CallAddbackRuntimeV5
import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV5.UpperBound

namespace EvmAsm.Evm64

open EvmWord EvmAsm.Rv64

/-- The n=4 v5 call trial quotient overestimates the normalized top-window
    quotient `(U4·2^64 + U3) / B3'` by at most 1, on the call path (no `U4 = 0`). -/
theorem n4CallAddbackBeqQHatV5_le_topwindow_div_plus_one {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hcall : isCallTrialN4 (a.getLimbN 3) (b.getLimbN 2) (b.getLimbN 3)) :
    (n4CallAddbackBeqQHatV5 a b).toNat ≤
      ((n4CallAddbackBeqU4 a b).toNat * 2 ^ 64 +
          (n4CallAddbackBeqU3 a b).toNat) /
        (n4CallAddbackBeqB3Prime b).toNat + 1 := by
  rw [n4CallAddbackBeqQHatV5_eq_normalized]
  have hB3 : (n4CallAddbackBeqB3Prime b).toNat ≥ 2 ^ 63 :=
    n4CallAddbackBeqB3Prime_ge_pow63 hb3nz
  have hu4_lt :
      (n4CallAddbackBeqU4 a b).toNat < (n4CallAddbackBeqB3Prime b).toNat := by
    have h_decomp := n4CallAddbackBeqU4_lt_vTop_of_call hcall
    rw [div128Quot_vTop_decomp (n4CallAddbackBeqB3Prime b)]
    simpa [divKTrialCallV4DHi, divKTrialCallV4DLo] using h_decomp
  exact div128Quot_v5_le_q_true_plus_one
    (n4CallAddbackBeqU4 a b) (n4CallAddbackBeqU3 a b) (n4CallAddbackBeqB3Prime b)
    hB3 hu4_lt

end EvmAsm.Evm64
