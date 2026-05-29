/-
  EvmAsm.Evm64.DivMod.Spec.N1V5CarryZero

  n=1 carry-zero discharged from shape over the **v5** schoolbook
  (`fullDivN1R3V5` / `iterN1V5` / `div128Quot_v5`).

  This is the v5 analog of `fullDivN1R3CarryZero_true_of_shape_*`
  (`N1CarryZeroReducers.lean`), but — crucially — it needs NO `Carry2NzAll`
  reachability hypothesis and NO `Div128AllPhasesNoWrapInv`. Because the v5
  trial is the exact 128/64 floor (`div128Quot_v5 = floor`, V5.4.5/V5.5.3), the
  single-limb mulsub leaves no borrow, so the iteration carry is zero — purely
  from the divisor shape. This sidesteps the false-universal `Carry2NzAll` that
  blocked the v4 n=1 lane. Bead evm-asm-wbc4i.9.1.
-/

import EvmAsm.Evm64.DivMod.Spec.N1CarryZeroReducers
import EvmAsm.Evm64.DivMod.Compose.FullPathN1V5Defs

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- **Abstract v5 single-limb carry-zero.** For a normalized one-limb divisor
    (`v0 ≥ 2^63`) in the call regime (`u1 < v0`), the v5 call-path iteration has
    zero carry: the v5 trial `div128Quot_v5 u1 u0 v0 ≤ floor` (V5.4.5), so
    `qHat·v0 ≤ u1·2^64 + u0` and the mulsub does not borrow. Mirrors
    `iterN1_true_carry_zero_of_v0_all_phases_no_wrap` but with NO
    `Div128AllPhasesNoWrapInv` hypothesis — the v5 floor bound is
    unconditional. -/
theorem iterN1V5_true_carry_zero_of_v0_norm_call
    (v0 u0 u1 : Word)
    (hv0_norm : v0.toNat ≥ 2^63)
    (hcall : u1.toNat < v0.toNat) :
    (iterN1V5 true v0 0 0 0 u0 u1 0 0 0).2.2.2.2.2 = 0 := by
  apply iterN1V5_true_carry_zero_of_mulsub_c3_zero
  · apply c3_un_zero_of_qHat_mul_le
    have hq_le := div128Quot_v5_le_q_true u1 u0 v0 hv0_norm hcall
    have h_product : (div128Quot_v5 u1 u0 v0).toNat * v0.toNat ≤
        u1.toNat * 2^64 + u0.toNat :=
      le_trans (Nat.mul_le_mul_right v0.toNat hq_le) (Nat.div_mul_le_self _ _)
    simp [EvmWord.val256]
    omega
  · rfl

/-- **v5 n=1 first-digit carry-zero, from shape (no `Carry2NzAll`).**
    `(fullDivN1R3V5 true …).carry = 0`, discharged unconditionally from the
    one-limb divisor shape: `normV.1 ≥ 2^63`
    (`fullDivN1NormV_limb0_ge_pow63_of_shape`) and the call regime
    `U_top < V0'` (`fullDivN1NormU_top_lt_normV_limb0_of_shape_shift_nz`). -/
theorem fullDivN1R3V5_carry_zero_of_shape
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0) :
    (fullDivN1R3V5 true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.2 = 0 := by
  unfold fullDivN1R3V5
  simp only [
    fullDivN1NormV_limb1_eq_zero_of_shape_shift_nz b0 b1 b2 b3 hb1z hshift_nz,
    fullDivN1NormV_limb2_eq_zero_of_shape b0 b1 b2 b3 hb1z hb2z,
    fullDivN1NormV_limb3_eq_zero_of_shape b0 b1 b2 b3 hb2z hb3z]
  exact iterN1V5_true_carry_zero_of_v0_norm_call _ _ _
    (fullDivN1NormV_limb0_ge_pow63_of_shape b0 b1 b2 b3 hbnz hb1z hb2z hb3z)
    (fullDivN1NormU_top_lt_normV_limb0_of_shape_shift_nz
      a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hshift_nz)

end EvmAsm.Evm64
