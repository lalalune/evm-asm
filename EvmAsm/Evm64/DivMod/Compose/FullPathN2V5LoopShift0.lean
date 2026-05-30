/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN2V5LoopShift0

  v5 n=2 shift=0 LOOP body (loopBodyOff → denormOff) over `divCode_noNop_v5`,
  with the carry hypothesis DISCHARGED FROM SHAPE.  The unified loop
  (`divK_loop_n2_unified_from_source_exact_loopIterScratch_v5_noNop_borrowCarry`,
  #7449) is GENERIC in the divisor/window values, so the shift=0 loop is that
  loop instantiated with the RAW divisor `(b0, b1, 0, 0)` and the shift=0
  u-window `(a2, a3, 0, 0, 0)` / `a1` / `a0`.  The carry is discharged via
  `loopN2SelectedBorrowCarryV5_shift0_of_shape` (#7469); the borrow flags are
  introduced in clean `ult (iterN2V5 …).2.2.1 b1` form.  The `hbltu_0` goal
  (#7449's `iterN2Max`/`iterWithDoubleAddback` THREADED form) is bridged to the
  clean PADDED form by rewriting the digit-2 `u3 = uTop = 0` collapse
  (`iterN2V5_collapse`, converted to `iterN2Max` form by `simp [iterN2V5]`).
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN2V5NoNopLoopUnifiedBorrowCarry
import EvmAsm.Evm64.DivMod.Spec.N2V5Shift0BundleOfShape

namespace EvmAsm.Evm64

open EvmWord EvmAsm.Rv64

theorem divK_loop_n2_shift0_from_shape_v5_noNop (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (a0 a1 a2 a3 b0 b1 q2Old q1Old q0Old raVal : Word)
    (retMem dMem dloMem scratchUn0 scratchMem : Word)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hb1ge : b1.toNat ≥ 2^63) :
    ∃ bltu_2 bltu_1 bltu_0 : Bool,
    cpsTripleWithin 702 (base + loopBodyOff) (base + denormOff)
      (divCode_noNop_v5 base)
      (loopN2PreWithScratchV4NoX1 sp jOld v5Old v6Old v7Old v10Old v11Old v2Old
        b0 b1 0 0 a2 a3 0 0 0 a1 a0 q2Old q1Old q0Old
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal))
      (loopN2UnifiedPostV5NoX1 bltu_2 bltu_1 bltu_0 sp base
        b0 b1 0 0 a2 a3 0 0 0 a1 a0
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal)) := by
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
  -- The three runtime borrow flags, in clean `ult (iterN2V5 …).2.2.1 b1` form.
  obtain ⟨bltu_2, hbltu_2⟩ : ∃ x, x = BitVec.ult (0 : Word) b1 := ⟨_, rfl⟩
  obtain ⟨bltu_1, hbltu_1⟩ :
      ∃ x, x = BitVec.ult (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 b1 := ⟨_, rfl⟩
  obtain ⟨bltu_0, hbltu_0⟩ :
      ∃ x, x = BitVec.ult (iterN2V5 bltu_1 b0 b1 0 0 a1
        (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.1
        (iterN2V5 bltu_2 b0 b1 0 0 a2 a3 0 0 0).2.2.1 0 0).2.2.1 b1 := ⟨_, rfl⟩
  -- Per-digit `bltu` path matches (shared by the collapse + carry bundle).
  have hc2 : bltu_2 = true → BitVec.ult (0:Word) b1 = true := fun h => by rw [← hbltu_2]; exact h
  have hm2 : bltu_2 = false → ¬ BitVec.ult (0:Word) b1 := fun h => by rw [← hbltu_2, h]; decide
  -- digit-2 remainder collapse (u3 = uTop = 0).
  obtain ⟨hR2u3, hR2uTop, _⟩ := iterN2V5_collapse bltu_2 b0 b1 a2 a3 0 hbnz hb1ge hfwv hc2 hm2
  refine ⟨bltu_2, bltu_1, bltu_0, ?_⟩
  apply divK_loop_n2_unified_from_source_exact_loopIterScratch_v5_noNop_borrowCarry
    bltu_2 bltu_1 bltu_0 sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
    b0 b1 0 0 a2 a3 0 0 0 a1 a0 q2Old q1Old q0Old raVal
    retMem dMem dloMem scratchUn0 scratchMem halign
  case hbltu_2 =>
    exact hbltu_2
  case hbltu_1 =>
    cases bltu_2 <;>
      simp only [iterN2V5, reduceIte, Bool.false_eq_true] at hbltu_1 ⊢ <;> exact hbltu_1
  case hbltu_0 =>
    cases bltu_2 <;> cases bltu_1 <;>
      simp only [iterN2V5, reduceIte, Bool.false_eq_true] at hR2u3 hR2uTop hbltu_0 ⊢ <;>
      rw [hR2u3, hR2uTop] <;> exact hbltu_0
  case hcarry =>
    exact loopN2SelectedBorrowCarryV5_shift0_of_shape a0 a1 a2 a3 b0 b1
      bltu_2 bltu_1 bltu_0 hb1ge hc2 hm2
      (fun h => by rw [← hbltu_1]; exact h)
      (fun h => by rw [← hbltu_1, h]; decide)
      (fun h => by rw [← hbltu_0]; exact h)
      (fun h => by rw [← hbltu_0, h]; decide)

end EvmAsm.Evm64
