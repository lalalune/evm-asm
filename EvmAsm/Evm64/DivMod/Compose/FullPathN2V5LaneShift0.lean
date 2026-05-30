/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN2V5LaneShift0

  Quotient-correctness prerequisite for the v5 n=2 DIV lane, shift=0 case.

  `n2_shift0_div_getLimbN_threaded`: the THREADED-digit form of the shift=0
  quotient correctness, `(EvmWord.div a b).getLimbN i = (n2Shift0R{0,1,2} …).1`,
  bridged from the PADDED form `n2_shift0_div_getLimbN_lane` (#7475) via the
  digit-2 / digit-1 remainder collapses (`iterN2V5_collapse`, telescoped exactly
  as in `n2_shift0_acc_quot`).  These are the `hdiv0..hdiv3` facts the forthcoming
  `evm_div_n2_lane_shift0_v5` feeds to the shift=0 post bridge.

  Bead `evm-asm-wbc4i.9.2.3`.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN2V5ParamShift0
import EvmAsm.Evm64.DivMod.Spec.N2V5Shift0DivLimb

namespace EvmAsm.Evm64

open EvmWord EvmAsm.Rv64

/-- THREADED-digit form of the shift=0 quotient correctness: the three v5 n=2
    threaded digit iterates (`n2Shift0R0/R1/R2`) give the limbs of
    `EvmWord.div a b`.  Bridges the PADDED `n2_shift0_div_getLimbN_lane` (#7475)
    by collapsing the digit-2 / digit-1 remainder tails to zero. -/
theorem n2_shift0_div_getLimbN_threaded (a b : EvmWord)
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
    (hc0 : bltu_0 = true → BitVec.ult (iterN2V5 bltu_1 b0 b1 0 0 a1
        (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1
        (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.2.1 b1 = true)
    (hm0 : bltu_0 = false → ¬ BitVec.ult (iterN2V5 bltu_1 b0 b1 0 0 a1
        (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1
        (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.2.1 b1) :
    (EvmWord.div a b).getLimbN 0 = (n2Shift0R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1).1 ∧
    (EvmWord.div a b).getLimbN 1 = (n2Shift0R1 bltu_2 bltu_1 a1 a2 a3 b0 b1).1 ∧
    (EvmWord.div a b).getLimbN 2 = (n2Shift0R2 bltu_2 a2 a3 b0 b1).1 ∧
    (EvmWord.div a b).getLimbN 3 = (0 : Word) := by
  obtain ⟨hd0, hd1, hd2, hd3⟩ := n2_shift0_div_getLimbN_lane a b a0 a1 a2 a3 b0 b1
    bltu_2 bltu_1 bltu_0 ha0 ha1 ha2 ha3 hb0 hb1 hb2z hb3z hb1ge hc2 hm2 hc1 hm1 hc0 hm0
  have h0 : (0:Word).toNat = 0 := rfl
  have hbnz : b0 ||| b1 ||| (0:Word) ||| 0 ≠ 0 := by
    intro h
    have h2 := (BitVec.or_eq_zero_iff.mp h).1
    have h3 := (BitVec.or_eq_zero_iff.mp h2).1
    have hz : b1 = 0 := (BitVec.or_eq_zero_iff.mp h3).2
    rw [hz] at hb1ge; simp at hb1ge
  have hvpos : 2^127 ≤ val256 b0 b1 0 0 := by simp only [EvmWord.val256, h0]; omega
  have hfwv : val256 a2 a3 0 0 < 2^64 * val256 b0 b1 0 0 := by
    have ha : val256 a2 a3 0 0 < 2^128 := by
      have := a2.isLt; have := a3.isLt; simp only [EvmWord.val256, h0]; omega
    calc val256 a2 a3 0 0 < 2^128 := ha
      _ ≤ 2^64 * 2^127 := by norm_num
      _ ≤ 2^64 * val256 b0 b1 0 0 := Nat.mul_le_mul_left _ hvpos
  obtain ⟨hR2u3, hR2uTop, _⟩ := iterN2V5_collapse bltu_2 b0 b1 a2 a3 0 hbnz hb1ge hfwv hc2 hm2
  have hR2 := iterN2V5_step bltu_2 b0 b1 a2 a3 0 hbnz hb1ge hfwv hc2 hm2
  have hR1valid := n2_next_window_lt a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1
    (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 _ hR2.2
  obtain ⟨hR1u3, hR1uTop, _⟩ := iterN2V5_collapse bltu_1 b0 b1 a1
    (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1
    (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 hbnz hb1ge hR1valid hc1 hm1
  refine ⟨?_, ?_, ?_, hd3⟩
  · simp only [n2Shift0R0, n2Shift0R1, n2Shift0R2]
    rw [hR2u3, hR2uTop, hR1u3, hR1uTop]; exact hd0
  · simp only [n2Shift0R1, n2Shift0R2]
    rw [hR2u3, hR2uTop]; exact hd1
  · simp only [n2Shift0R2]; exact hd2

end EvmAsm.Evm64
