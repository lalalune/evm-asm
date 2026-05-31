/-
  EvmAsm.Evm64.DivMod.Spec.N2V5Shift0RemainderLane

  Lane-ready (`a b : EvmWord`) form of the n=2 v5 SHIFT=0 remainder-word
  correctness: the shift=0 schoolbook remainder word equals `EvmWord.mod a b`,
  given the n=2 shape (`b2=b3=0`, top divisor limb `b1 ≥ 2^63` i.e. shift=0) and
  the per-digit `bltu` path matches.  Bridges the `fromLimbs`-form
  `n2_shift0_remainder_eq_mod` to the `a b` form via
  `EvmWord.fromLimbs_match_getLimbN_id` (with the `b2=b3=0` padding discharged by
  the shape).  MOD counterpart of `n2_shift0_quotient_word_eq_div_lane`;
  the `hmodWord` the n=2 shift=0 MOD lane feeds to its post bridge.
-/

import EvmAsm.Evm64.DivMod.Spec.N2V5Shift0Quotient

namespace EvmAsm.Evm64

open EvmWord EvmAsm.Rv64

/-- Lane form of the shift=0 n=2 remainder word: equals `EvmWord.mod a b`. -/
theorem n2_shift0_remainder_word_eq_mod_lane (a b : EvmWord)
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
    EvmWord.fromLimbs (fun i : Fin 4 => match i with
        | 0 => (iterN2V5 bltu_0 b0 b1 0 0 a0 (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.1 (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.2.1 0 0).2.1
        | 1 => (iterN2V5 bltu_0 b0 b1 0 0 a0 (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.1 (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.2.1 0 0).2.2.1
        | 2 => (iterN2V5 bltu_0 b0 b1 0 0 a0 (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.1 (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.2.1 0 0).2.2.2.1
        | 3 => (iterN2V5 bltu_0 b0 b1 0 0 a0 (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.1 (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.2.1 0 0).2.2.2.2.1)
      = EvmWord.mod a b := by
  have hbase := n2_shift0_remainder_eq_mod a0 a1 a2 a3 b0 b1 hb1ge bltu_2 bltu_1 bltu_0
    hc2 hm2 hc1 hm1 hc0 hm0
  refine hbase.trans ?_
  congr 1
  · conv_rhs => rw [← EvmWord.fromLimbs_match_getLimbN_id a]
    congr 1
    funext i
    fin_cases i <;> simp only [ha0, ha1, ha2, ha3]
  · conv_rhs => rw [← EvmWord.fromLimbs_match_getLimbN_id b]
    congr 1
    funext i
    fin_cases i <;> simp only [hb0, hb1, hb2z, hb3z]

end EvmAsm.Evm64
