/-
  EvmAsm.Evm64.DivMod.Spec.N4C3LeU4Plus2

  The n=4 call-path mulsub borrow `c3 ≤ U4 + 2`, UNCONDITIONALLY (no `U4 = 0`):
  the U4-general counterpart of `n4CallAddbackBeq_mulsub_c3_le_two_of_u4_zero`
  (N4C3LeTwo).

  Composes the generic `mulsubN4_c3_le_u4_plus_two` (#7646) with the n=4 trial
  `+2` overestimate against the FULL five-limb normalized dividend, obtained
  unconditionally from:
  * `n4CallAddbackBeqNormalized_div_eq_qTrue` (`UNormVal / BNormVal = qTrue`,
    scale-invariance — no `U4 = 0`), and
  * `n4CallAddbackBeqQHatV5_le_qTrue_plus_two_of_call` (`qHat ≤ qTrue + 2`, #7573).

  On the addback branch (`u4 < c3`), this bounds the corrective addback count
  `c3 - u4 ≤ 2` for ANY `U4` — the double-addback (carry2) path then corrects the
  trial without the `U4 = 0` restriction of the merged single-addback chain.
  Bead `evm-asm-wbc4i.8.2.2.4`.
-/

import EvmAsm.Evm64.EvmWordArith.DivMulsubC3LeU4Plus2
import EvmAsm.Evm64.DivMod.Spec.N4QHatBound

namespace EvmAsm.Evm64

open EvmWord EvmAsm.Rv64

/-- The n=4 call-path mulsub carry-out `c3` is at most `U4 + 2` — UNCONDITIONALLY
    (no `U4 = 0`). -/
theorem n4CallAddbackBeq_mulsub_c3_le_u4_plus_two {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hcall : isCallTrialN4 (a.getLimbN 3) (b.getLimbN 2) (b.getLimbN 3)) :
    (mulsubN4 (n4CallAddbackBeqQHatV5 a b)
        (n4CallAddbackBeqB0Prime b) (n4CallAddbackBeqB1Prime b)
        (n4CallAddbackBeqB2Prime b) (n4CallAddbackBeqB3Prime b)
        (n4CallAddbackBeqU0 a b) (n4CallAddbackBeqU1 a b)
        (n4CallAddbackBeqU2 a b) (n4CallAddbackBeqU3 a b)).2.2.2.2.toNat ≤
      (n4CallAddbackBeqU4 a b).toNat + 2 := by
  apply mulsubN4_c3_le_u4_plus_two (n4CallAddbackBeqU4 a b).toNat
    (n4CallAddbackBeqNormalizedDivisor_ne_zero hb3nz)
  -- remaining goal: qHat ≤ (U4·2^256 + val256 U0..U3) / val256 B0'..B3' + 2
  have hUN : (n4CallAddbackBeqU4 a b).toNat * 2 ^ 256 +
      val256 (n4CallAddbackBeqU0 a b) (n4CallAddbackBeqU1 a b)
        (n4CallAddbackBeqU2 a b) (n4CallAddbackBeqU3 a b) =
      n4CallAddbackBeqUNormVal a b := by
    unfold n4CallAddbackBeqUNormVal; ring
  rw [hUN]
  show (n4CallAddbackBeqQHatV5 a b).toNat ≤
      n4CallAddbackBeqUNormVal a b / n4CallAddbackBeqBNormVal b + 2
  rw [n4CallAddbackBeqNormalized_div_eq_qTrue hshift_nz]
  exact n4CallAddbackBeqQHatV5_le_qTrue_plus_two_of_call hb3nz hshift_nz hcall

end EvmAsm.Evm64
