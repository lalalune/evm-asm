/-
  EvmAsm.Evm64.DivMod.Spec.N2V5Shift0Quotient

  **v5 n=2 accumulated quotient correctness for the shift=0 path.**
  When the divisor's top limb `b1` is already normalized (`b1 ≥ 2^63`, i.e.
  `clz b1 = 0`), the algorithm skips normalization and runs the schoolbook
  directly on the RAW divisor `(b0,b1,0,0)` and the raw dividend limbs.  The
  three v5 n=2 digits then combine to exactly `val256 a / val256 b`.

  This is the shift=0 counterpart of `fullDivN2_acc_quot_eq_div_of_shape`
  (N2V5NormScaled, shift≠0).  It is cleaner: with `s = 0` there is no
  normalization scaling, so the per-digit steps (`iterN2V5_step`, over the raw
  2-limb divisor) telescope directly into the unnormalized Euclidean equation,
  and `Nat.div_mod_unique` recovers the quotient.  Bead `evm-asm-wbc4i.9.2`.
-/

import EvmAsm.Evm64.DivMod.Spec.N2V5NormScaled
import EvmAsm.Evm64.DivMod.Spec.N2QuotientWord

namespace EvmAsm.Evm64

open EvmWord EvmAsm.Rv64

/-- **v5 n=2 accumulated quotient correctness (shift=0).** The three v5 n=2
    digits over the raw 2-limb divisor combine to `val256 a / val256 b`. -/
theorem n2_shift0_acc_quot
    (a0 a1 a2 a3 b0 b1 : Word) (hb1 : b1.toNat ≥ 2^63) (bltu_2 bltu_1 bltu_0 : Bool)
    (hc2 : bltu_2 = true → BitVec.ult (0:Word) b1 = true)
    (hm2 : bltu_2 = false → ¬ BitVec.ult (0:Word) b1)
    (hc1 : bltu_1 = true → BitVec.ult (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 b1 = true)
    (hm1 : bltu_1 = false → ¬ BitVec.ult (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 b1)
    (hc0 : bltu_0 = true → BitVec.ult (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.2.1 b1 = true)
    (hm0 : bltu_0 = false → ¬ BitVec.ult (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.2.1 b1) :
    (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).1.toNat * 2^128
      + (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).1.toNat * 2^64
      + (iterN2V5 bltu_0 b0 b1 0 0 a0 (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.1 (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.2.1 0 0).1.toNat
      = val256 a0 a1 a2 a3 / val256 b0 b1 0 0 := by
  have h0 : (0:Word).toNat = 0 := rfl
  have hbnz : b0 ||| b1 ||| 0 ||| 0 ≠ 0 := by
    intro h; have h2 := (BitVec.or_eq_zero_iff.mp h).1; have h3 := (BitVec.or_eq_zero_iff.mp h2).1
    have hz : b1 = 0 := (BitVec.or_eq_zero_iff.mp h3).2; rw [hz] at hb1; simp at hb1
  have hvpos : 2^127 ≤ val256 b0 b1 0 0 := by simp only [EvmWord.val256, h0]; omega
  have hfwv : val256 a2 a3 0 0 < 2^64 * val256 b0 b1 0 0 := by
    have ha : val256 a2 a3 0 0 < 2^128 := by
      have := a2.isLt; have := a3.isLt; simp only [EvmWord.val256, h0]; omega
    calc val256 a2 a3 0 0 < 2^128 := ha
      _ ≤ 2^64 * 2^127 := by norm_num
      _ ≤ 2^64 * val256 b0 b1 0 0 := Nat.mul_le_mul_left _ hvpos
  have hR2 := iterN2V5_step bltu_2 b0 b1 a2 a3 0 hbnz hb1 hfwv hc2 hm2
  have hR1valid := n2_next_window_lt a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 _ hR2.2
  have hR1 := iterN2V5_step bltu_1 b0 b1 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 hbnz hb1 hR1valid hc1 hm1
  have hR0valid := n2_next_window_lt a0 (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.1 (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.2.1 _ hR1.2
  have hR0 := iterN2V5_step bltu_0 b0 b1 a0 (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.1 (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.2.1 hbnz hb1 hR0valid hc0 hm0
  have hfirst : val256 a0 a1 a2 a3 = a0.toNat + 2^64*a1.toNat + 2^128*(a2.toNat + 2^64*a3.toNat + 2^128*(0:Nat)) := by
    simp only [EvmWord.val256]; ring
  have hW2 : val256 a2 a3 0 0 = a2.toNat + 2^64*a3.toNat + 2^128*(0:Nat) := by
    simp only [EvmWord.val256, h0]; ring
  have hWin1 : val256 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0
      = a1.toNat + 2^64*((iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1.toNat + 2^64*(iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1.toNat) := by
    simp only [EvmWord.val256, h0]; ring
  have hWin0 : val256 a0 (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.1 (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.2.1 0
      = a0.toNat + 2^64*((iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.1.toNat + 2^64*(iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.2.1.toNat) := by
    simp only [EvmWord.val256, h0]; ring
  rw [hW2] at hR2; rw [hWin1] at hR1; rw [hWin0] at hR0
  have htele := fullDivN2V5_three_step_nat hfirst hR2.1 hR1.1 hR0.1
  have hbpos : 0 < val256 b0 b1 0 0 := by omega
  symm
  exact ((Nat.div_mod_unique hbpos).mpr ⟨by rw [htele]; ring, hR0.2⟩).1

/-- **v5 n=2 MOD remainder correctness (shift=0).** At shift=0 the remainder is
    used directly (no denormalization), so the final R0 remainder limbs equal
    `EvmWord.mod a b`.  Cleaner than the shift≠0 case (#7367): `s = 0`, so the
    denorm is the identity and `mod_of_val256_eq_mod` applies after collapsing the
    remainder to its low two limbs. -/
theorem n2_shift0_remainder_eq_mod
    (a0 a1 a2 a3 b0 b1 : Word) (hb1 : b1.toNat ≥ 2^63) (bltu_2 bltu_1 bltu_0 : Bool)
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
      = EvmWord.mod
          (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3)
          (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => b0 | 1 => b1 | 2 => 0 | 3 => 0) := by
  have h0 : (0:Word).toNat = 0 := rfl
  have hbnz : b0 ||| b1 ||| (0:Word) ||| 0 ≠ 0 := by
    intro h; have h2 := (BitVec.or_eq_zero_iff.mp h).1; have h3 := (BitVec.or_eq_zero_iff.mp h2).1
    have hz : b1 = 0 := (BitVec.or_eq_zero_iff.mp h3).2; rw [hz] at hb1; simp at hb1
  have hvpos : 2^127 ≤ val256 b0 b1 0 0 := by simp only [EvmWord.val256, h0]; omega
  have hfwv : val256 a2 a3 0 0 < 2^64 * val256 b0 b1 0 0 := by
    have ha : val256 a2 a3 0 0 < 2^128 := by
      have := a2.isLt; have := a3.isLt; simp only [EvmWord.val256, h0]; omega
    calc val256 a2 a3 0 0 < 2^128 := ha
      _ ≤ 2^64 * 2^127 := by norm_num
      _ ≤ 2^64 * val256 b0 b1 0 0 := Nat.mul_le_mul_left _ hvpos
  have hR2 := iterN2V5_step bltu_2 b0 b1 a2 a3 0 hbnz hb1 hfwv hc2 hm2
  have hR1valid := n2_next_window_lt a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 _ hR2.2
  have hR1 := iterN2V5_step bltu_1 b0 b1 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 hbnz hb1 hR1valid hc1 hm1
  have hR0valid := n2_next_window_lt a0 (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.1 (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.2.1 _ hR1.2
  have hR0 := iterN2V5_step bltu_0 b0 b1 a0 (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.1 (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.2.1 hbnz hb1 hR0valid hc0 hm0
  have hR0c := iterN2V5_collapse bltu_0 b0 b1 a0 (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.1 (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.2.1 hbnz hb1 hR0valid hc0 hm0
  have hfirst : val256 a0 a1 a2 a3 = a0.toNat + 2^64*a1.toNat + 2^128*(a2.toNat + 2^64*a3.toNat + 2^128*(0:Nat)) := by
    simp only [EvmWord.val256]; ring
  have hW2 : val256 a2 a3 0 0 = a2.toNat + 2^64*a3.toNat + 2^128*(0:Nat) := by
    simp only [EvmWord.val256, h0]; ring
  have hWin1 : val256 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0
      = a1.toNat + 2^64*((iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1.toNat + 2^64*(iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1.toNat) := by
    simp only [EvmWord.val256, h0]; ring
  have hWin0 : val256 a0 (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.1 (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.2.1 0
      = a0.toNat + 2^64*((iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.1.toNat + 2^64*(iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.2.1.toNat) := by
    simp only [EvmWord.val256, h0]; ring
  rw [hW2] at hR2; rw [hWin1] at hR1; rw [hWin0] at hR0
  have htele := fullDivN2V5_three_step_nat hfirst hR2.1 hR1.1 hR0.1
  have hbpos : 0 < val256 b0 b1 0 0 := by omega
  have hmodeq : val256 a0 a1 a2 a3 % val256 b0 b1 0 0
      = (iterN2V5 bltu_0 b0 b1 0 0 a0 (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.1 (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.2.1 0 0).2.1.toNat
        + 2^64*(iterN2V5 bltu_0 b0 b1 0 0 a0 (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.1 (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.2.1 0 0).2.2.1.toNat := by
    rw [htele, Nat.mul_comm _ (val256 b0 b1 0 0), Nat.mul_add_mod, Nat.mod_eq_of_lt hR0.2]
  have hr : val256
      (iterN2V5 bltu_0 b0 b1 0 0 a0 (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.1 (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.2.1 0 0).2.1
      (iterN2V5 bltu_0 b0 b1 0 0 a0 (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.1 (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.2.1 0 0).2.2.1
      (iterN2V5 bltu_0 b0 b1 0 0 a0 (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.1 (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.2.1 0 0).2.2.2.1
      (iterN2V5 bltu_0 b0 b1 0 0 a0 (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.1 (iterN2V5 bltu_1 b0 b1 0 0 a1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1 (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.2.1 0 0).2.2.2.2.1
      = val256 a0 a1 a2 a3 % val256 b0 b1 0 0 := by
    rw [hR0c.1, hR0c.2.1, hmodeq]; simp only [EvmWord.val256, h0]; ring_nf
  exact mod_of_val256_eq_mod hbnz hr

end EvmAsm.Evm64
