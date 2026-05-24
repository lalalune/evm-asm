/-
  EvmAsm.Evm64.DivMod.Spec.CallSkipV4

  v4 analogues of the call+skip semantic predicate and `EvmWord.div`
  getLimbN bridge originally proven for the v1 algorithm in
  `Spec/CallSkip.lean`.

  Provides:

  * `n4CallSkipSemanticHoldsV4 a b : Prop` — Knuth-A lower bound at the
    val256 level for the v4 trial quotient `div128Quot_v4` (mirror of
    `n4CallSkipSemanticHolds`).
  * `n4_call_skip_div_mod_getLimbN_v4` — under `hbnz`, `hshift_nz`, the
    v4 skip-borrow runtime check `isSkipBorrowN4CallV4Evm`, and `hsem :=
    n4CallSkipSemanticHoldsV4 a b`, identifies the four limbs of
    `EvmWord.div a b` with the v4 trial quotient (low limb) and `0`
    (upper three limbs).

  Together with the no-overflow bound
  `div128Quot_v4_call_skip_mul_val256_b_le_val256_a` (see
  `EvmWordArith/Div128CallSkipCloseV4.lean`), the bridge sandwiches
  `qHat_v4.toNat` to `val256(a)/val256(b)`.

  The `hsem` precondition is left as an input here; its unconditional
  discharge under runtime conditions (v4 Knuth-A) is tracked separately
  by bead `evm-asm-9iqmw.7.1.3.1.1`.
-/
import EvmAsm.Evm64.DivMod.Spec.CallSkip
import EvmAsm.Evm64.EvmWordArith.Div128CallSkipCloseV4
import EvmAsm.Evm64.DivMod.Compose.FullPathN4V4

namespace EvmAsm.Evm64

open EvmAsm.Rv64 EvmWord
open EvmAsm.Rv64.AddrNorm (word_add_zero)

/-- **v4 algorithmic lower bound for `div128Quot_v4` at val256 level.**

    Mirror of `n4CallSkipSemanticHolds` (Spec/CallSkip.lean:1067), with
    the v1 trial `div128Quot` replaced by the v4 trial `div128Quot_v4`.

    Packages Knuth Theorem A (normalized divisor version) for the v4
    algorithm: `val256(a)/val256(b) ≤ qHat_v4`. The v4 algorithm with
    classical 2-correction in both Phase-1b and Phase-2 satisfies this
    bound (it computes the exact 128/64 quotient when `un21 < vTop`,
    and the val256 Knuth-A follows). The discharge under runtime
    conditions is left to a separate bead. -/
def n4CallSkipSemanticHoldsV4 (a b : EvmWord) : Prop :=
  let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
  let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
  let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
  let u4 := (a.getLimbN 3) >>> antiShift
  let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
  val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
      val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ≤
    (div128Quot_v4 u4 u3 b3').toNat

theorem n4CallSkipSemanticHoldsV4_def {a b : EvmWord} :
    n4CallSkipSemanticHoldsV4 a b =
    (let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
     let antiShift :=
       (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
     let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
     let u4 := (a.getLimbN 3) >>> antiShift
     let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
     val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
         val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ≤
       (div128Quot_v4 u4 u3 b3').toNat) :=
  rfl

/-- **v4 getLimbN bridge for the n=4 call+skip path.**

    Mirror of `n4_call_skip_div_mod_getLimbN` (Spec/CallSkip.lean:1134),
    with the v1 algorithm replaced by `div128Quot_v4` and the v1 borrow
    predicate `isSkipBorrowN4CallEvm` replaced by its v4 counterpart
    `isSkipBorrowN4CallV4Evm`.

    Proof structure (transfers verbatim — qHat-agnostic sandwich):
    1. From T3 (v4): `qHat.toNat * val256(b) ≤ val256(a)`.
    2. From hsem (Knuth-A v4): `val256(a)/val256(b) ≤ qHat.toNat`.
    3. Sandwich gives `qHat.toNat = a.toNat / b.toNat = (EvmWord.div a b).toNat`.
    4. Since `qHat.toNat < 2^64`, only the low limb of `EvmWord.div a b` is
       non-zero; the upper three limbs vanish. -/
theorem n4_call_skip_div_mod_getLimbN_v4 (a b : EvmWord)
    (hbnz : b ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hborrow : isSkipBorrowN4CallV4Evm a b)
    (hsem : n4CallSkipSemanticHoldsV4 a b) :
    let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
    let antiShift :=
      (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
    let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
    let u4 := (a.getLimbN 3) >>> antiShift
    let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
    let qHat := div128Quot_v4 u4 u3 b3'
    (EvmWord.div a b).getLimbN 0 = qHat ∧
    (EvmWord.div a b).getLimbN 1 = 0 ∧
    (EvmWord.div a b).getLimbN 2 = 0 ∧
    (EvmWord.div a b).getLimbN 3 = 0 := by
  intro shift antiShift b3' u4 u3 qHat
  rw [isSkipBorrowN4CallV4Evm_def] at hborrow
  rw [n4CallSkipSemanticHoldsV4_def] at hsem
  have hT3 := div128Quot_v4_call_skip_mul_val256_b_le_val256_a
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      hshift_nz hborrow
  change qHat.toNat * val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ≤
         val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) at hT3
  change val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
         val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ≤
         qHat.toNat at hsem
  have ha_val : val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      = a.toNat := by
    simp only [← EvmWord.getLimb_as_getLimbN_0, ← EvmWord.getLimb_as_getLimbN_1,
               ← EvmWord.getLimb_as_getLimbN_2, ← EvmWord.getLimb_as_getLimbN_3]
    exact EvmWord.val256_eq_toNat a
  have hb_val : val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      = b.toNat := by
    simp only [← EvmWord.getLimb_as_getLimbN_0, ← EvmWord.getLimb_as_getLimbN_1,
               ← EvmWord.getLimb_as_getLimbN_2, ← EvmWord.getLimb_as_getLimbN_3]
    exact EvmWord.val256_eq_toNat b
  have hb_pos : 0 < b.toNat := by
    rcases Nat.eq_zero_or_pos b.toNat with h | h
    · exfalso; apply hbnz; exact BitVec.eq_of_toNat_eq (by simp [h])
    · exact h
  rw [ha_val, hb_val] at hT3 hsem
  have hq_eq : qHat.toNat = a.toNat / b.toNat := by
    have hle : qHat.toNat ≤ a.toNat / b.toNat :=
      (Nat.le_div_iff_mul_le hb_pos).mpr hT3
    omega
  have hdiv_toNat : (EvmWord.div a b).toNat = a.toNat / b.toNat := by
    unfold EvmWord.div
    rw [if_neg hbnz]
    exact BitVec.toNat_udiv
  set q_target : EvmWord := EvmWord.fromLimbs fun i : Fin 4 =>
    match i with | 0 => qHat | 1 => 0 | 2 => 0 | 3 => 0 with hq_target
  have hq_target_toNat : q_target.toNat = qHat.toNat := by
    simp [q_target, EvmWord.fromLimbs_toNat]
  have hq_eq_div : q_target = EvmWord.div a b :=
    BitVec.eq_of_toNat_eq (by omega)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hq_eq_div]; exact EvmWord.getLimbN_fromLimbs_0
  · rw [← hq_eq_div]; exact EvmWord.getLimbN_fromLimbs_1
  · rw [← hq_eq_div]; exact EvmWord.getLimbN_fromLimbs_2
  · rw [← hq_eq_div]; exact EvmWord.getLimbN_fromLimbs_3

/-- **EvmWord-form wrapper of `evm_div_n4_full_call_skip_spec_v4`.**
    Mirror of `evm_div_n4_full_call_skip_stack_pre_spec` (the v1 wrapper
    at `Spec/CallSkip.lean:323`), adapted for the v4 surface:

    * code: `divCode_v4 base` (instead of `divCode base`).
    * borrow predicate: `isSkipBorrowN4CallV4Evm` (instead of v1).
    * pre includes the v4 trial-call scratch cell `(sp + 3936) ↦ₘ scratchMem`.
    * post is `fullDivN4CallSkipPostV4` (v4 post — exposes `div128Quot_v4`).

    Translates Word-form limbs (a0..a3, b0..b3) to EvmWord (a, b) via
    `getLimbN`. -/
theorem evm_div_n4_full_call_skip_stack_pre_spec_v4 (sp base : Word)
    (a b : EvmWord) (v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (hbnz : b ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu : isCallTrialN4Evm a b)
    (hborrow : isSkipBorrowN4CallV4Evm a b) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 148 + 2 + 23 + 10)
      base (base + nopOff) (divCode_v4 base)
      ((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) **
       (.x2 ↦ᵣ (clzResult (b.getLimbN 3)).2 >>> (63 : Nat)) **
       (.x9 ↦ᵣ signExtend12 (4 : BitVec 12) - (4 : Word)) **
       (.x11 ↦ᵣ v11Old) **
       evmWordIs sp a ** evmWordIs (sp + 32) b **
       divScratchValuesCall sp q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old
         u5 u6 u7 shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (fullDivN4CallSkipPostV4 sp base
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
        scratchMem) := by
  have hbnz' : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0 :=
    (EvmWord.ne_zero_iff_getLimbN_or).mp hbnz
  rw [isCallTrialN4Evm_def] at hbltu
  rw [isSkipBorrowN4CallV4Evm_def] at hborrow
  have hraw := evm_div_n4_full_call_skip_spec_v4 sp base
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
    hbnz' hb3nz hshift_nz halign hbltu hborrow
  exact cpsTripleWithin_weaken
    (fun h hp => by
      rw [evmWordIs_sp_limbs_eq sp a _ _ _ _ rfl rfl rfl rfl,
          evmWordIs_sp32_limbs_eq sp b _ _ _ _ rfl rfl rfl rfl,
          divScratchValuesCall_unfold, divScratchValues_unfold] at hp
      rw [word_add_zero]
      xperm_hyp hp)
    (fun _ hq => hq)
    hraw

end EvmAsm.Evm64
