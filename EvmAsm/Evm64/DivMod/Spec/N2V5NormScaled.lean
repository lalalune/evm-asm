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
import EvmAsm.Evm64.EvmWordArith.DivN2NormVStructure

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

/-- **First-digit (R2) step over the normalized window.** Rewrites
    `fullDivN2R2V5` to expose `iterN2V5` over the 2-limb `normV` (using the
    shift≠0 shape lemmas) and applies the unified per-digit step
    `iterN2V5_step`.  Gives the clean 2-limb Euclidean step
    `val256(nu2,nu3,nu4,0) = q2·val256 normV + R2r` with `R2r < val256 normV`,
    from window-validity + the `bltu_2` path match.  First link of the
    cross-digit telescope for `fullDivN2QuotientWordV5_eq_div_of_shape`. -/
theorem fullDivN2R2V5_step_of_shape (a0 a1 a2 a3 b0 b1 b2 b3 : Word) (bltu_2 : Bool)
    (hb2z : b2 = 0) (hb3z : b3 = 0) (hshift_nz : (clzResult b1).1 ≠ 0) (hb1nz : b1 ≠ 0)
    (hvalid : val256 (fullDivN2NormU a0 a1 a2 a3 b1).2.2.1
        (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1 (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2 0
        < 2^64 * val256 (fullDivN2NormV b0 b1 b2 b3).1 (fullDivN2NormV b0 b1 b2 b3).2.1 0 0)
    (hcall : bltu_2 = true →
      BitVec.ult (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2 (fullDivN2NormV b0 b1 b2 b3).2.1 = true)
    (hmax : bltu_2 = false →
      ¬ BitVec.ult (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2 (fullDivN2NormV b0 b1 b2 b3).2.1) :
    val256 (fullDivN2NormU a0 a1 a2 a3 b1).2.2.1
        (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1 (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2 0 =
      (fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1.toNat *
        val256 (fullDivN2NormV b0 b1 b2 b3).1 (fullDivN2NormV b0 b1 b2 b3).2.1 0 0 +
        ((fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.1.toNat +
          2^64 * (fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1.toNat) ∧
      (fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.1.toNat +
          2^64 * (fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1.toNat <
        val256 (fullDivN2NormV b0 b1 b2 b3).1 (fullDivN2NormV b0 b1 b2 b3).2.1 0 0 := by
  have hv2 := fullDivN2NormV_v2_zero_of_shape_shift_nz b0 b1 b2 b3 hb2z hshift_nz
  have hv3 := fullDivN2NormV_top_zero_of_shape b0 b1 b2 b3 hb3z hb2z
  have hmsb := fullDivN2NormV_msb_of_b1_ne_zero b0 b1 b2 b3 hb1nz
  have hbnz : (fullDivN2NormV b0 b1 b2 b3).1 ||| (fullDivN2NormV b0 b1 b2 b3).2.1 ||| 0 ||| 0 ≠ 0 := by
    intro h
    have h2 := (BitVec.or_eq_zero_iff.mp h).1
    have h3 := (BitVec.or_eq_zero_iff.mp h2).1
    have hz : (fullDivN2NormV b0 b1 b2 b3).2.1 = 0 := (BitVec.or_eq_zero_iff.mp h3).2
    rw [hz] at hmsb; simp at hmsb
  have hrw : fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3 =
      iterN2V5 bltu_2 (fullDivN2NormV b0 b1 b2 b3).1 (fullDivN2NormV b0 b1 b2 b3).2.1 0 0
        (fullDivN2NormU a0 a1 a2 a3 b1).2.2.1 (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.1
        (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2 0 0 := by
    unfold fullDivN2R2V5; dsimp only; rw [hv2, hv3]
  rw [hrw]
  exact iterN2V5_step bltu_2 _ _ _ _ _ hbnz hmsb hvalid hcall hmax

end EvmAsm.Evm64
