/-
  EvmAsm.Evm64.DivMod.Spec.N2V5NormScaled

  The n=2 val256-scaling normalization bridges — the divisor and dividend, after
  the CLZ-of-`b1` left shift, have value equal to the original scaled by
  `2^shift` (with the dividend carrying an overflow limb).

  These are the n=2 analogs of `fullDivN1NormU_val256_eq_scaled` /
  `fullDivN1NormV_val256_eq_scaled_of_shape` (N1QuotientStackBridge), proved the
  same way via the generic `EvmWord.val256_normalize{,_general}` + `antiShift_toNat_mod_eq`.

  They connect the per-digit steps over the NORMALIZED window
  (`iterN2V5_step`, N2V5RemainderLt) to the original `a / b`: the normalized
  Euclidean `val256 normU = Q·val256 normV + R` plus these bridges gives
  `val256 a·2^s = Q·(val256 b·2^s) + R`, which `div_quotient_of_normalized`
  turns into `Q = val256 a / val256 b`.  This is the corrected (shift-aware)
  assembly route — replacing the shift=0-only, funnel-degenerate
  `fullDivN2MulSubEqV5`.  Bead `evm-asm-wbc4i.9.2`.
-/

import EvmAsm.Evm64.DivMod.Spec.N2V5RemainderLt
import EvmAsm.Evm64.DivMod.Spec.N1QuotientStackBridge

namespace EvmAsm.Evm64

open EvmWord EvmAsm.Rv64

/-- **n=2 normalized dividend value (with overflow) = original scaled.** The
    CLZ-of-`b1` normalization of the dividend satisfies
    `val256 normU + overflow·2^256 = val256 a · 2^shift`.  n=2 analog of
    `fullDivN1NormU_val256_eq_scaled`. -/
theorem fullDivN2NormU_val256_eq_scaled
    (a0 a1 a2 a3 b1 : Word) (hshift_nz : (clzResult b1).1 ≠ 0) :
    EvmWord.val256
      (fullDivN2NormU a0 a1 a2 a3 b1).1
      (fullDivN2NormU a0 a1 a2 a3 b1).2.1
      (fullDivN2NormU a0 a1 a2 a3 b1).2.2.1
      (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1 +
      (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2.toNat * 2^256 =
    EvmWord.val256 a0 a1 a2 a3 * 2^(fullDivN2Shift b1).toNat := by
  unfold fullDivN2NormU fullDivN2AntiShift
  dsimp only
  unfold fullDivN2Shift
  have h_shift_pos : 1 ≤ (clzResult b1).1.toNat := by
    rcases Nat.eq_zero_or_pos (clzResult b1).1.toNat with h | h
    · exfalso; apply hshift_nz; exact BitVec.eq_of_toNat_eq (by simp [h])
    · exact h
  have hsmod : (clzResult b1).1.toNat % 64 = (clzResult b1).1.toNat :=
    Nat.mod_eq_of_lt (by have := clzResult_fst_toNat_le b1; omega)
  rw [hsmod, antiShift_toNat_mod_eq h_shift_pos (clzResult_fst_toNat_le b1)]
  exact EvmWord.val256_normalize_general h_shift_pos (by omega) a0 a1 a2 a3

/-- **n=2 normalized divisor value = original scaled (from 2-limb shape).** For a
    2-limb divisor (`b2 = b3 = 0`), the CLZ-of-`b1` normalization satisfies
    `val256 normV = val256 b · 2^shift`.  n=2 analog of
    `fullDivN1NormV_val256_eq_scaled_of_shape`. -/
theorem fullDivN2NormV_val256_eq_scaled_of_shape
    (b0 b1 b2 b3 : Word) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b1).1 ≠ 0) :
    EvmWord.val256
      (fullDivN2NormV b0 b1 b2 b3).1
      (fullDivN2NormV b0 b1 b2 b3).2.1
      (fullDivN2NormV b0 b1 b2 b3).2.2.1
      (fullDivN2NormV b0 b1 b2 b3).2.2.2 =
    EvmWord.val256 b0 b1 b2 b3 * 2^(fullDivN2Shift b1).toNat := by
  subst b2; subst b3
  unfold fullDivN2NormV fullDivN2AntiShift
  dsimp only
  unfold fullDivN2Shift
  have h_shift_pos : 1 ≤ (clzResult b1).1.toNat := by
    rcases Nat.eq_zero_or_pos (clzResult b1).1.toNat with h | h
    · exfalso; apply hshift_nz; exact BitVec.eq_of_toNat_eq (by simp [h])
    · exact h
  have hsmod : (clzResult b1).1.toNat % 64 = (clzResult b1).1.toNat :=
    Nat.mod_eq_of_lt (by have := clzResult_fst_toNat_le b1; omega)
  rw [hsmod, antiShift_toNat_mod_eq h_shift_pos (clzResult_fst_toNat_le b1)]
  exact EvmWord.val256_normalize h_shift_pos (by omega) b0 b1 0 0 (by simp)

end EvmAsm.Evm64
