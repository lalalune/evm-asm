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

/-- A nonzero original top divisor limb makes the normalized n=4 divisor
    nonzero, as required by double-addback value conservation. -/
theorem n4CallAddbackBeqNormalizedDivisor_ne_zero {b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0) :
    n4CallAddbackBeqB0Prime b ||| n4CallAddbackBeqB1Prime b |||
        n4CallAddbackBeqB2Prime b ||| n4CallAddbackBeqB3Prime b ≠ 0 := by
  intro h_zero
  have h_b3_zero : n4CallAddbackBeqB3Prime b = 0 := by
    bv_decide
  have h_top_ge := n4CallAddbackBeqB3Prime_ge_pow63 hb3nz
  rw [h_b3_zero] at h_top_ge
  have h_zero_toNat : (0 : Word).toNat = 0 := by decide
  rw [h_zero_toNat] at h_top_ge
  norm_num at h_top_ge

/-- Positivity of the normalized n=4 divisor value from the original runtime
    top-limb nonzero condition. -/
theorem n4CallAddbackBeqNormalizedDivisor_pos {b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0) :
    0 < EvmWord.val256
      (n4CallAddbackBeqB0Prime b)
      (n4CallAddbackBeqB1Prime b)
      (n4CallAddbackBeqB2Prime b)
      (n4CallAddbackBeqB3Prime b) :=
  val256_pos_of_or_ne_zero (n4CallAddbackBeqNormalizedDivisor_ne_zero hb3nz)

/-- Normalized five-limb dividend value used by the v4 n=4 call-addback path. -/
def n4CallAddbackBeqUNormVal (a b : EvmWord) : Nat :=
  EvmWord.val256
      (n4CallAddbackBeqU0 a b)
      (n4CallAddbackBeqU1 a b)
      (n4CallAddbackBeqU2 a b)
      (n4CallAddbackBeqU3 a b) +
    (n4CallAddbackBeqU4 a b).toNat * 2^256

/-- Normalized divisor value used by the v4 n=4 call-addback path. -/
def n4CallAddbackBeqBNormVal (b : EvmWord) : Nat :=
  EvmWord.val256
    (n4CallAddbackBeqB0Prime b)
    (n4CallAddbackBeqB1Prime b)
    (n4CallAddbackBeqB2Prime b)
    (n4CallAddbackBeqB3Prime b)

/-- Lower four limbs of the normalized dividend used by the v4 n=4 trial
    quotient bound. The overflow limb is tracked separately in `UNormVal`. -/
def n4CallAddbackBeqULoNormVal (a b : EvmWord) : Nat :=
  EvmWord.val256
    (n4CallAddbackBeqU0 a b)
    (n4CallAddbackBeqU1 a b)
    (n4CallAddbackBeqU2 a b)
    (n4CallAddbackBeqU3 a b)

/-- Iterator output used by the v4 n=4 call-addback path. -/
def n4CallAddbackBeqIterOut (a b : EvmWord) :=
  iterWithDoubleAddback
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

/-- Normalized remainder value returned by the v4 n=4 call-addback iterator. -/
def n4CallAddbackBeqIterRNormVal (a b : EvmWord) : Nat :=
  let out := n4CallAddbackBeqIterOut a b
  EvmWord.val256 out.2.1 out.2.2.1 out.2.2.2.1 out.2.2.2.2.1 +
    out.2.2.2.2.2.toNat * 2^256

/-- Compact arithmetic obligations left after the runtime branch predicates:
    the v4 trial quotient is within one of the lower normalized quotient, and
    the corrected iterator remainder is below the normalized divisor. -/
def n4CallAddbackBeqRuntimeBounds (a b : EvmWord) : Prop :=
  (n4CallAddbackBeqQHatV4 a b).toNat ≤
      n4CallAddbackBeqULoNormVal a b / n4CallAddbackBeqBNormVal b + 1 ∧
    n4CallAddbackBeqIterRNormVal a b < n4CallAddbackBeqBNormVal b

/-- Runtime-normalized c3 bridge: if the normalized trial quotient is within
    one of the normalized true quotient, the raw borrow condition pins the
    mulsub carry-out to one. -/
theorem n4CallAddbackBeqC3_eq_one_of_borrow_and_qhat_le_div_plus_one {a b : EvmWord}
    (hbnz :
      n4CallAddbackBeqB0Prime b ||| n4CallAddbackBeqB1Prime b |||
        n4CallAddbackBeqB2Prime b ||| n4CallAddbackBeqB3Prime b ≠ 0)
    (hq_over :
      (n4CallAddbackBeqQHatV4 a b).toNat ≤
        EvmWord.val256
          (n4CallAddbackBeqU0 a b)
          (n4CallAddbackBeqU1 a b)
          (n4CallAddbackBeqU2 a b)
          (n4CallAddbackBeqU3 a b) /
          EvmWord.val256
            (n4CallAddbackBeqB0Prime b)
            (n4CallAddbackBeqB1Prime b)
            (n4CallAddbackBeqB2Prime b)
            (n4CallAddbackBeqB3Prime b) + 1)
    (h_borrow :
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
          (n4CallAddbackBeqU3 a b)).2.2.2.2) :
      (mulsubN4
        (n4CallAddbackBeqQHatV4 a b)
        (n4CallAddbackBeqB0Prime b)
        (n4CallAddbackBeqB1Prime b)
        (n4CallAddbackBeqB2Prime b)
        (n4CallAddbackBeqB3Prime b)
        (n4CallAddbackBeqU0 a b)
        (n4CallAddbackBeqU1 a b)
        (n4CallAddbackBeqU2 a b)
        (n4CallAddbackBeqU3 a b)).2.2.2.2 = 1 := by
  apply mulsubN4_c3_ne_zero_imp_one hbnz hq_over
  intro h_zero
  rw [h_zero] at h_borrow
  simp [BitVec.ult] at h_borrow

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

/-- Runtime-condition value conservation using a normalized `qHat ≤ qTrue + 1`
    bound to discharge the c3=1-on-borrow side condition. -/
theorem n4CallAddbackBeqIterWithDoubleAddback_val256_conservation_of_runtime_qhat_le_div_plus_one
    {a b : EvmWord}
    (hbnz :
      n4CallAddbackBeqB0Prime b ||| n4CallAddbackBeqB1Prime b |||
        n4CallAddbackBeqB2Prime b ||| n4CallAddbackBeqB3Prime b ≠ 0)
    (hq_over :
      (n4CallAddbackBeqQHatV4 a b).toNat ≤
        EvmWord.val256
          (n4CallAddbackBeqU0 a b)
          (n4CallAddbackBeqU1 a b)
          (n4CallAddbackBeqU2 a b)
          (n4CallAddbackBeqU3 a b) /
          EvmWord.val256
            (n4CallAddbackBeqB0Prime b)
            (n4CallAddbackBeqB1Prime b)
            (n4CallAddbackBeqB2Prime b)
            (n4CallAddbackBeqB3Prime b) + 1)
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
  exact n4CallAddbackBeqIterWithDoubleAddback_val256_conservation_of_runtime
    hbnz
    (n4CallAddbackBeqC3_eq_one_of_borrow_and_qhat_le_div_plus_one hbnz hq_over)
    h_carry2

/-- Runtime-condition value conservation with the original top-limb nonzero
    runtime condition discharging normalized divisor nonzero. -/
theorem n4CallAddbackBeqIterWithDoubleAddback_val256_conservation_of_runtime_top_nonzero
    {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hq_over :
      (n4CallAddbackBeqQHatV4 a b).toNat ≤
        EvmWord.val256
          (n4CallAddbackBeqU0 a b)
          (n4CallAddbackBeqU1 a b)
          (n4CallAddbackBeqU2 a b)
          (n4CallAddbackBeqU3 a b) /
          EvmWord.val256
            (n4CallAddbackBeqB0Prime b)
            (n4CallAddbackBeqB1Prime b)
            (n4CallAddbackBeqB2Prime b)
            (n4CallAddbackBeqB3Prime b) + 1)
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
  exact n4CallAddbackBeqIterWithDoubleAddback_val256_conservation_of_runtime_qhat_le_div_plus_one
    (n4CallAddbackBeqNormalizedDivisor_ne_zero hb3nz)
    hq_over
    h_carry2

/-- Runtime-condition value conservation with the iterator quotient rewritten
    to the named v4 call-addback quotient output. -/
theorem n4CallAddbackBeqQOutV4_val256_conservation_of_runtime_top_nonzero
    {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hq_over :
      (n4CallAddbackBeqQHatV4 a b).toNat ≤
        EvmWord.val256
          (n4CallAddbackBeqU0 a b)
          (n4CallAddbackBeqU1 a b)
          (n4CallAddbackBeqU2 a b)
          (n4CallAddbackBeqU3 a b) /
          EvmWord.val256
            (n4CallAddbackBeqB0Prime b)
            (n4CallAddbackBeqB1Prime b)
            (n4CallAddbackBeqB2Prime b)
            (n4CallAddbackBeqB3Prime b) + 1)
    (h_borrow : isAddbackBorrowN4CallV4Evm a b)
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
      (n4CallAddbackBeqQOutV4 a b).toNat * EvmWord.val256
        (n4CallAddbackBeqB0Prime b)
        (n4CallAddbackBeqB1Prime b)
        (n4CallAddbackBeqB2Prime b)
        (n4CallAddbackBeqB3Prime b) +
      EvmWord.val256 out.2.1 out.2.2.1 out.2.2.2.1 out.2.2.2.2.1 +
      out.2.2.2.2.2.toNat * 2^256 := by
  have h := n4CallAddbackBeqIterWithDoubleAddback_val256_conservation_of_runtime_top_nonzero
    hb3nz hq_over h_carry2
  dsimp only at h ⊢
  rw [n4CallAddbackBeqIterWithDoubleAddback_qOutV4_of_runtime_borrow h_borrow] at h
  exact h

/-- Compact form of the runtime-condition value conservation theorem. -/
theorem n4CallAddbackBeqQOutV4_conservation_compact
    {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hq_over :
      (n4CallAddbackBeqQHatV4 a b).toNat ≤
        EvmWord.val256
          (n4CallAddbackBeqU0 a b)
          (n4CallAddbackBeqU1 a b)
          (n4CallAddbackBeqU2 a b)
          (n4CallAddbackBeqU3 a b) /
          EvmWord.val256
            (n4CallAddbackBeqB0Prime b)
            (n4CallAddbackBeqB1Prime b)
            (n4CallAddbackBeqB2Prime b)
            (n4CallAddbackBeqB3Prime b) + 1)
    (h_borrow : isAddbackBorrowN4CallV4Evm a b)
    (h_carry2 : isAddbackCarry2NzN4CallV4Evm a b) :
    n4CallAddbackBeqUNormVal a b =
      (n4CallAddbackBeqQOutV4 a b).toNat * n4CallAddbackBeqBNormVal b +
        n4CallAddbackBeqIterRNormVal a b := by
  have h := n4CallAddbackBeqQOutV4_val256_conservation_of_runtime_top_nonzero
    hb3nz hq_over h_borrow h_carry2
  dsimp [n4CallAddbackBeqUNormVal, n4CallAddbackBeqBNormVal,
    n4CallAddbackBeqIterRNormVal, n4CallAddbackBeqIterOut] at h ⊢
  simpa [Nat.add_assoc] using h

/-- Pure quotient extraction for the call-addback conservation shape. -/
theorem quotient_eq_div_of_mul_add_remainder_lt {aVal bVal qVal rVal : Nat}
    (hb_pos : 0 < bVal)
    (h_eq : aVal = qVal * bVal + rVal)
    (h_rem_lt : rVal < bVal) :
    qVal = aVal / bVal := by
  rw [h_eq]
  rw [Nat.add_comm]
  rw [Nat.add_mul_div_right _ _ hb_pos]
  rw [Nat.div_eq_of_lt h_rem_lt]
  rw [Nat.zero_add]

/-- Runtime-condition quotient extraction from the compact conservation shape,
    assuming the compact normalized remainder is below the normalized divisor. -/
theorem n4CallAddbackBeqQOutV4_toNat_eq_normalized_div_of_runtime_top_nonzero
    {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hq_over :
      (n4CallAddbackBeqQHatV4 a b).toNat ≤
        EvmWord.val256
          (n4CallAddbackBeqU0 a b)
          (n4CallAddbackBeqU1 a b)
          (n4CallAddbackBeqU2 a b)
          (n4CallAddbackBeqU3 a b) /
          EvmWord.val256
            (n4CallAddbackBeqB0Prime b)
            (n4CallAddbackBeqB1Prime b)
            (n4CallAddbackBeqB2Prime b)
            (n4CallAddbackBeqB3Prime b) + 1)
    (h_borrow : isAddbackBorrowN4CallV4Evm a b)
    (h_carry2 : isAddbackCarry2NzN4CallV4Evm a b)
    (h_rem_lt : n4CallAddbackBeqIterRNormVal a b < n4CallAddbackBeqBNormVal b) :
    (n4CallAddbackBeqQOutV4 a b).toNat =
      n4CallAddbackBeqUNormVal a b / n4CallAddbackBeqBNormVal b := by
  exact quotient_eq_div_of_mul_add_remainder_lt
    (by
      simpa [n4CallAddbackBeqBNormVal] using
        n4CallAddbackBeqNormalizedDivisor_pos hb3nz)
    (n4CallAddbackBeqQOutV4_conservation_compact
      hb3nz hq_over h_borrow h_carry2)
    h_rem_lt

/-- The compact normalized quotient target is the original unnormalized
    `qTrue`, since both dividend and divisor were scaled by the same CLZ
    normalization factor. -/
theorem n4CallAddbackBeqNormalized_div_eq_qTrue
    {a b : EvmWord}
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0) :
    n4CallAddbackBeqUNormVal a b / n4CallAddbackBeqBNormVal b =
      n4CallAddbackBeqQTrue a b := by
  have h_norm_u := u_val256_eq_scaled_with_overflow
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 3) hshift_nz
  have h_norm_b := b3_prime_val256_eq_scaled
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    hshift_nz
  rw [n4CallAddbackBeqQTrue_unfold]
  rw [n4CallAddbackBeqUNormVal, n4CallAddbackBeqBNormVal]
  rw [n4CallAddbackBeqU0_unfold, n4CallAddbackBeqU1_unfold,
    n4CallAddbackBeqU2_unfold, n4CallAddbackBeqU3_unfold,
    n4CallAddbackBeqU4_unfold, n4CallAddbackBeqB0Prime_unfold,
    n4CallAddbackBeqB1Prime_unfold, n4CallAddbackBeqB2Prime_unfold,
    n4CallAddbackBeqB3Prime_unfold, n4CallAddbackBeqShift_unfold,
    n4CallAddbackBeqAntiShift_unfold]
  rw [h_norm_u, h_norm_b]
  exact val256_div_scale_invariant
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    (clzResult (b.getLimbN 3)).1.toNat

/-- Runtime-condition semantic bridge after the normalized quotient target has
    been identified with the original unnormalized `qTrue`. -/
theorem n4CallAddbackBeqSemanticHoldsV4_of_runtime_top_nonzero
    {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hq_over :
      (n4CallAddbackBeqQHatV4 a b).toNat ≤
        EvmWord.val256
          (n4CallAddbackBeqU0 a b)
          (n4CallAddbackBeqU1 a b)
          (n4CallAddbackBeqU2 a b)
          (n4CallAddbackBeqU3 a b) /
          EvmWord.val256
            (n4CallAddbackBeqB0Prime b)
            (n4CallAddbackBeqB1Prime b)
            (n4CallAddbackBeqB2Prime b)
            (n4CallAddbackBeqB3Prime b) + 1)
    (h_borrow : isAddbackBorrowN4CallV4Evm a b)
    (h_carry2 : isAddbackCarry2NzN4CallV4Evm a b)
    (h_rem_lt : n4CallAddbackBeqIterRNormVal a b < n4CallAddbackBeqBNormVal b)
    (h_norm_div :
      n4CallAddbackBeqUNormVal a b / n4CallAddbackBeqBNormVal b =
        n4CallAddbackBeqQTrue a b) :
    n4CallAddbackBeqSemanticHoldsV4 a b := by
  apply n4CallAddbackBeqSemanticHoldsV4_of_qOutV4_toNat_eq_qTrue
  rw [n4CallAddbackBeqQOutV4_toNat_eq_normalized_div_of_runtime_top_nonzero
    hb3nz hq_over h_borrow h_carry2 h_rem_lt]
  exact h_norm_div

/-- Runtime-condition semantic bridge after discharging the normalized-divisor
    scaling step from the CLZ shift nonzero condition. -/
theorem n4CallAddbackBeqSemanticHoldsV4_of_runtime_conditions
    {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hq_over :
      (n4CallAddbackBeqQHatV4 a b).toNat ≤
        EvmWord.val256
          (n4CallAddbackBeqU0 a b)
          (n4CallAddbackBeqU1 a b)
          (n4CallAddbackBeqU2 a b)
          (n4CallAddbackBeqU3 a b) /
          EvmWord.val256
            (n4CallAddbackBeqB0Prime b)
            (n4CallAddbackBeqB1Prime b)
            (n4CallAddbackBeqB2Prime b)
            (n4CallAddbackBeqB3Prime b) + 1)
    (h_borrow : isAddbackBorrowN4CallV4Evm a b)
    (h_carry2 : isAddbackCarry2NzN4CallV4Evm a b)
    (h_rem_lt : n4CallAddbackBeqIterRNormVal a b < n4CallAddbackBeqBNormVal b) :
    n4CallAddbackBeqSemanticHoldsV4 a b :=
  n4CallAddbackBeqSemanticHoldsV4_of_runtime_top_nonzero
    hb3nz hq_over h_borrow h_carry2 h_rem_lt
    (n4CallAddbackBeqNormalized_div_eq_qTrue hshift_nz)

/-- Compact runtime-condition semantic bridge with the qhat-over side
    condition stated using named normalized values. -/
theorem n4CallAddbackBeqSemanticHoldsV4_of_runtime_conditions_compact
    {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hq_over :
      (n4CallAddbackBeqQHatV4 a b).toNat ≤
        n4CallAddbackBeqULoNormVal a b / n4CallAddbackBeqBNormVal b + 1)
    (h_borrow : isAddbackBorrowN4CallV4Evm a b)
    (h_carry2 : isAddbackCarry2NzN4CallV4Evm a b)
    (h_rem_lt : n4CallAddbackBeqIterRNormVal a b < n4CallAddbackBeqBNormVal b) :
    n4CallAddbackBeqSemanticHoldsV4 a b :=
  n4CallAddbackBeqSemanticHoldsV4_of_runtime_conditions
    hb3nz hshift_nz
    (by
      simpa [n4CallAddbackBeqULoNormVal, n4CallAddbackBeqBNormVal] using hq_over)
    h_borrow h_carry2 h_rem_lt

/-- Runtime-condition semantic bridge with the remaining compact arithmetic
    bounds bundled as one named predicate. -/
theorem n4CallAddbackBeqSemanticHoldsV4_of_runtime_bounds
    {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (h_bounds : n4CallAddbackBeqRuntimeBounds a b)
    (h_borrow : isAddbackBorrowN4CallV4Evm a b)
    (h_carry2 : isAddbackCarry2NzN4CallV4Evm a b) :
    n4CallAddbackBeqSemanticHoldsV4 a b :=
  n4CallAddbackBeqSemanticHoldsV4_of_runtime_conditions_compact
    hb3nz hshift_nz h_bounds.1 h_borrow h_carry2 h_bounds.2

end EvmWord

end EvmAsm.Evm64
