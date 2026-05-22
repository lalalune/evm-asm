/-
  EvmAsm.Evm64.DivMod.Spec.CallAddbackRuntime

  Runtime-condition bridges for the n=4 v4 call+addback semantic marker.
-/

import EvmAsm.Evm64.DivMod.Spec.CallAddback

namespace EvmAsm.Evm64

open EvmAsm.Rv64

namespace EvmWord

/-- The packaged v4 n=4 call-addback runtime borrow predicate implies the raw
    addback branch condition consumed by `iterWithDoubleAddback`. -/
theorem n4CallAddbackBeqBorrow_raw_of_runtime {a b : EvmWord}
    (h_borrow : isAddbackBorrowN4CallV4Evm a b) :
    BitVec.ult (n4CallAddbackBeqU4 a b)
      (mulsubN4
        (n4CallAddbackBeqQHatV4 a b)
        (n4CallAddbackBeqB0Prime b)
        (n4CallAddbackBeqB1Prime b)
        (n4CallAddbackBeqB2Prime b)
        (n4CallAddbackBeqB3Prime b)
        (n4CallAddbackBeqU0 a b)
        (n4CallAddbackBeqU1 a b)
        (n4CallAddbackBeqU2 a b)
        (n4CallAddbackBeqU3 a b)).2.2.2.2 := by
  rw [isAddbackBorrowN4CallV4Evm_def] at h_borrow
  unfold isAddbackBorrowN4CallV4Ab at h_borrow
  unfold loopBodyN4CallAddbackBorrowV4 at h_borrow
  simp_rw [divKTrialCallV4QHat_eq_div128Quot_v4] at h_borrow
  unfold n4CallAddbackBeqB0Prime n4CallAddbackBeqB1Prime
    n4CallAddbackBeqB2Prime n4CallAddbackBeqB3Prime
    n4CallAddbackBeqU0 n4CallAddbackBeqU1 n4CallAddbackBeqU2
    n4CallAddbackBeqU3 n4CallAddbackBeqU4 n4CallAddbackBeqQHatV4
    n4CallAddbackBeqShift n4CallAddbackBeqAntiShift
  by_cases h_branch :
      (a.getLimbN 3 >>>
        ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64)).ult
        (mulsubN4_c3
          (div128Quot_v4
            (a.getLimbN 3 >>>
              ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64))
            (a.getLimbN 3 <<< ((clzResult (b.getLimbN 3)).1.toNat % 64) |||
              a.getLimbN 2 >>>
                ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64))
            (b.getLimbN 3 <<< ((clzResult (b.getLimbN 3)).1.toNat % 64) |||
              b.getLimbN 2 >>>
                ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64)))
          (b.getLimbN 0 <<< ((clzResult (b.getLimbN 3)).1.toNat % 64))
          (b.getLimbN 1 <<< ((clzResult (b.getLimbN 3)).1.toNat % 64) |||
            b.getLimbN 0 >>>
              ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64))
          (b.getLimbN 2 <<< ((clzResult (b.getLimbN 3)).1.toNat % 64) |||
            b.getLimbN 1 >>>
              ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64))
          (b.getLimbN 3 <<< ((clzResult (b.getLimbN 3)).1.toNat % 64) |||
            b.getLimbN 2 >>>
              ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64))
          (a.getLimbN 0 <<< ((clzResult (b.getLimbN 3)).1.toNat % 64))
          (a.getLimbN 1 <<< ((clzResult (b.getLimbN 3)).1.toNat % 64) |||
            a.getLimbN 0 >>>
              ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64))
          (a.getLimbN 2 <<< ((clzResult (b.getLimbN 3)).1.toNat % 64) |||
            a.getLimbN 1 >>>
              ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64))
          (a.getLimbN 3 <<< ((clzResult (b.getLimbN 3)).1.toNat % 64) |||
            a.getLimbN 2 >>>
              ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64)))
  · simpa [mulsubN4_c3] using h_branch
  · rw [if_neg h_branch] at h_borrow
    exact False.elim (h_borrow rfl)

/-- Runtime-borrow form of the addback iterator quotient bridge. -/
theorem n4CallAddbackBeqIterWithDoubleAddback_qOutV4_of_runtime_borrow {a b : EvmWord}
    (h_borrow : isAddbackBorrowN4CallV4Evm a b) :
    (iterWithDoubleAddback
      (n4CallAddbackBeqQHatV4 a b)
      (n4CallAddbackBeqB0Prime b)
      (n4CallAddbackBeqB1Prime b)
      (n4CallAddbackBeqB2Prime b)
      (n4CallAddbackBeqB3Prime b)
      (n4CallAddbackBeqU0 a b)
      (n4CallAddbackBeqU1 a b)
      (n4CallAddbackBeqU2 a b)
      (n4CallAddbackBeqU3 a b)
      (n4CallAddbackBeqU4 a b)).1 =
      n4CallAddbackBeqQOutV4 a b :=
  n4CallAddbackBeqIterWithDoubleAddback_qOutV4_of_borrow
    (n4CallAddbackBeqBorrow_raw_of_runtime h_borrow)

/-- The packaged v4 n=4 call-addback runtime carry2 predicate is the raw
    double-addback progress predicate over the normalized marker limbs. -/
theorem n4CallAddbackBeqCarry2Nz_of_runtime {a b : EvmWord}
    (h_carry2 : isAddbackCarry2NzN4CallV4Evm a b) :
    isAddbackCarry2Nz
      (n4CallAddbackBeqQHatV4 a b)
      (n4CallAddbackBeqB0Prime b)
      (n4CallAddbackBeqB1Prime b)
      (n4CallAddbackBeqB2Prime b)
      (n4CallAddbackBeqB3Prime b)
      (n4CallAddbackBeqU0 a b)
      (n4CallAddbackBeqU1 a b)
      (n4CallAddbackBeqU2 a b)
      (n4CallAddbackBeqU3 a b)
      (n4CallAddbackBeqU4 a b) := by
  have h_raw := isAddbackCarry2NzN4CallV4Evm_raw h_carry2
  simp_rw [divKTrialCallV4QHat_eq_div128Quot_v4] at h_raw
  rw [n4CallAddbackBeqQHatV4_eq_normalized]
  unfold isAddbackCarry2Nz
  unfold n4CallAddbackBeqB0Prime n4CallAddbackBeqB1Prime
    n4CallAddbackBeqB2Prime n4CallAddbackBeqB3Prime
    n4CallAddbackBeqU0 n4CallAddbackBeqU1 n4CallAddbackBeqU2
    n4CallAddbackBeqU3 n4CallAddbackBeqU4 n4CallAddbackBeqShift
    n4CallAddbackBeqAntiShift
  simpa using h_raw

/-- Runtime-condition wrapper for double-addback value conservation over the
    normalized n=4 v4 call+addback marker limbs. -/
theorem n4CallAddbackBeqIterWithDoubleAddback_val256_conservation_of_runtime
    {a b : EvmWord}
    (hbnz :
      n4CallAddbackBeqB0Prime b ||| n4CallAddbackBeqB1Prime b |||
        n4CallAddbackBeqB2Prime b ||| n4CallAddbackBeqB3Prime b ≠ 0)
    (hc3_one_of_borrow :
      BitVec.ult (n4CallAddbackBeqU4 a b)
        (mulsubN4
          (n4CallAddbackBeqQHatV4 a b)
          (n4CallAddbackBeqB0Prime b)
          (n4CallAddbackBeqB1Prime b)
          (n4CallAddbackBeqB2Prime b)
          (n4CallAddbackBeqB3Prime b)
          (n4CallAddbackBeqU0 a b)
          (n4CallAddbackBeqU1 a b)
          (n4CallAddbackBeqU2 a b)
          (n4CallAddbackBeqU3 a b)).2.2.2.2 →
        (mulsubN4
          (n4CallAddbackBeqQHatV4 a b)
          (n4CallAddbackBeqB0Prime b)
          (n4CallAddbackBeqB1Prime b)
          (n4CallAddbackBeqB2Prime b)
          (n4CallAddbackBeqB3Prime b)
          (n4CallAddbackBeqU0 a b)
          (n4CallAddbackBeqU1 a b)
          (n4CallAddbackBeqU2 a b)
          (n4CallAddbackBeqU3 a b)).2.2.2.2 = 1)
    (h_carry2 : isAddbackCarry2NzN4CallV4Evm a b) :
    let out := iterWithDoubleAddback
      (n4CallAddbackBeqQHatV4 a b)
      (n4CallAddbackBeqB0Prime b)
      (n4CallAddbackBeqB1Prime b)
      (n4CallAddbackBeqB2Prime b)
      (n4CallAddbackBeqB3Prime b)
      (n4CallAddbackBeqU0 a b)
      (n4CallAddbackBeqU1 a b)
      (n4CallAddbackBeqU2 a b)
      (n4CallAddbackBeqU3 a b)
      (n4CallAddbackBeqU4 a b)
    EvmWord.val256
        (n4CallAddbackBeqU0 a b)
        (n4CallAddbackBeqU1 a b)
        (n4CallAddbackBeqU2 a b)
        (n4CallAddbackBeqU3 a b) +
      (n4CallAddbackBeqU4 a b).toNat * 2^256 =
      out.1.toNat * EvmWord.val256
        (n4CallAddbackBeqB0Prime b)
        (n4CallAddbackBeqB1Prime b)
        (n4CallAddbackBeqB2Prime b)
        (n4CallAddbackBeqB3Prime b) +
      EvmWord.val256 out.2.1 out.2.2.1 out.2.2.2.1 out.2.2.2.2.1 +
      out.2.2.2.2.2.toNat * 2^256 := by
  exact iterWithDoubleAddback_val256_conservation_of_carry2
    (n4CallAddbackBeqQHatV4 a b)
    (n4CallAddbackBeqB0Prime b)
    (n4CallAddbackBeqB1Prime b)
    (n4CallAddbackBeqB2Prime b)
    (n4CallAddbackBeqB3Prime b)
    (n4CallAddbackBeqU0 a b)
    (n4CallAddbackBeqU1 a b)
    (n4CallAddbackBeqU2 a b)
    (n4CallAddbackBeqU3 a b)
    (n4CallAddbackBeqU4 a b)
    hbnz
    hc3_one_of_borrow
    (n4CallAddbackBeqCarry2Nz_of_runtime h_carry2)

end EvmWord

end EvmAsm.Evm64
