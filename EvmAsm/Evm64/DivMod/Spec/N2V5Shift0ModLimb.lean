/-
  EvmAsm.Evm64.DivMod.Spec.N2V5Shift0ModLimb

  Per-limb form of the n=2 v5 SHIFT=0 remainder correctness: each limb of
  `EvmWord.mod a b` equals the corresponding shift=0 schoolbook remainder limb
  (the raw final `iterN2V5 …`-based remainder window).  Decomposes the
  remainder-word equality `n2_shift0_remainder_word_eq_mod_lane` into the four
  `(EvmWord.mod a b).getLimbN i = rem_i` equalities via `getLimbN_fromLimbs_*`.
  These are the `hmod0..hmod3` facts the n=2 shift=0 MOD lane feeds to its post
  bridge.  MOD mirror of `n2_shift0_div_getLimbN_lane`.
-/

import EvmAsm.Evm64.DivMod.Spec.N2V5Shift0RemainderLane
import EvmAsm.Evm64.EvmWordArith.DivLimbBridge

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- The four `(EvmWord.mod a b).getLimbN i` shift=0 digit equalities. -/
theorem n2_shift0_mod_getLimbN_lane (a b : EvmWord)
    (a0 a1 a2 a3 b0 b1 : Word) (bltu_2 bltu_1 bltu_0 : Bool)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2z : b.getLimbN 2 = 0) (hb3z : b.getLimbN 3 = 0)
    (hb1ge : b1.toNat ≥ 2^63)
    (hc2 : bltu_2 = true → BitVec.ult (0:Word) b1 = true)
    (hm2 : bltu_2 = false → ¬ BitVec.ult (0:Word) b1)
    (hc1 : bltu_1 = true → BitVec.ult (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 b1 = true)
    (hm1 : bltu_1 = false → ¬ BitVec.ult (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 b1)
    (hc0 : bltu_0 = true → BitVec.ult (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.2.1 b1 = true)
    (hm0 : bltu_0 = false → ¬ BitVec.ult (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.2.1 b1) :
    (EvmWord.mod a b).getLimbN 0 =
        (iterN2V5 bltu_0 b0 b1 0 0 a0 (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.1 (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.2.1 0 0).2.1 ∧
    (EvmWord.mod a b).getLimbN 1 =
        (iterN2V5 bltu_0 b0 b1 0 0 a0 (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.1 (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.2.1 0 0).2.2.1 ∧
    (EvmWord.mod a b).getLimbN 2 =
        (iterN2V5 bltu_0 b0 b1 0 0 a0 (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.1 (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.2.1 0 0).2.2.2.1 ∧
    (EvmWord.mod a b).getLimbN 3 =
        (iterN2V5 bltu_0 b0 b1 0 0 a0 (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.1 (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.2.1 0 0).2.2.2.2.1 := by
  have hword := n2_shift0_remainder_word_eq_mod_lane a b a0 a1 a2 a3 b0 b1 bltu_2 bltu_1 bltu_0
    ha0 ha1 ha2 ha3 hb0 hb1 hb2z hb3z hb1ge hc2 hm2 hc1 hm1 hc0 hm0
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [← hword]
  · exact EvmWord.getLimbN_fromLimbs_0
  · exact EvmWord.getLimbN_fromLimbs_1
  · exact EvmWord.getLimbN_fromLimbs_2
  · exact EvmWord.getLimbN_fromLimbs_3

end EvmAsm.Evm64
