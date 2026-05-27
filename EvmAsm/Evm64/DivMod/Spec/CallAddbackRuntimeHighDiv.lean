/-
  EvmAsm.Evm64.DivMod.Spec.CallAddbackRuntimeHighDiv

  Small N4 call-addback runtime bridge lemmas that keep
  CallAddbackRuntime.lean below the file-size guardrail.
-/

import EvmAsm.Evm64.DivMod.Spec.CallAddbackRuntime

namespace EvmAsm.Evm64

namespace EvmWord

/-- High 128/64 quotient used by the n=4 call-addback Knuth-A bridge. -/
def n4CallAddbackBeqHighDivVal (a b : EvmWord) : Nat :=
  ((n4CallAddbackBeqU4 a b).toNat * 2^64 +
      (n4CallAddbackBeqU3 a b).toNat) /
    (n4CallAddbackBeqB3Prime b).toNat

/-- The v4 call-addback qhat is no larger than the high 128/64 quotient. -/
def n4CallAddbackBeqQHatHighDivBound (a b : EvmWord) : Prop :=
  (n4CallAddbackBeqQHatV4 a b).toNat ≤
    n4CallAddbackBeqHighDivVal a b

/-- Knuth-A denominator bridge for the n=4 call-addback path.

    The v4 counterexample invalidated the stronger `≤ normDiv` target; this is
    the surviving `+1` shape used by the runtime-bounds bridge. -/
def n4CallAddbackBeqHighDivKnuthABound (a b : EvmWord) : Prop :=
  n4CallAddbackBeqHighDivVal a b ≤
    n4CallAddbackBeqULoNormVal a b / n4CallAddbackBeqBNormVal b + 1

theorem n4CallAddbackBeqHighDivVal_def {a b : EvmWord} :
    n4CallAddbackBeqHighDivVal a b =
      ((n4CallAddbackBeqU4 a b).toNat * 2^64 +
          (n4CallAddbackBeqU3 a b).toNat) /
        (n4CallAddbackBeqB3Prime b).toNat :=
  rfl

theorem n4CallAddbackBeqQHatHighDivBound_def {a b : EvmWord} :
    n4CallAddbackBeqQHatHighDivBound a b =
      ((n4CallAddbackBeqQHatV4 a b).toNat ≤
        n4CallAddbackBeqHighDivVal a b) :=
  rfl

theorem n4CallAddbackBeqHighDivKnuthABound_def {a b : EvmWord} :
    n4CallAddbackBeqHighDivKnuthABound a b =
      (n4CallAddbackBeqHighDivVal a b ≤
        n4CallAddbackBeqULoNormVal a b / n4CallAddbackBeqBNormVal b + 1) :=
  rfl

theorem n4CallAddbackBeqQHatHighDivBound.of_le {a b : EvmWord}
    (h_qhat_le_high_div :
      (n4CallAddbackBeqQHatV4 a b).toNat ≤
        ((n4CallAddbackBeqU4 a b).toNat * 2^64 +
            (n4CallAddbackBeqU3 a b).toNat) /
          (n4CallAddbackBeqB3Prime b).toNat) :
    n4CallAddbackBeqQHatHighDivBound a b := by
  rwa [n4CallAddbackBeqQHatHighDivBound_def,
    n4CallAddbackBeqHighDivVal_def]

theorem n4CallAddbackBeqHighDivKnuthABound.of_le {a b : EvmWord}
    (h_high_div_le_norm_plus_one :
      ((n4CallAddbackBeqU4 a b).toNat * 2^64 +
          (n4CallAddbackBeqU3 a b).toNat) /
        (n4CallAddbackBeqB3Prime b).toNat ≤
          n4CallAddbackBeqULoNormVal a b / n4CallAddbackBeqBNormVal b + 1) :
    n4CallAddbackBeqHighDivKnuthABound a b := by
  rwa [n4CallAddbackBeqHighDivKnuthABound_def,
    n4CallAddbackBeqHighDivVal_def]

theorem n4CallAddbackBeqQHatHighDivBound.of_floor_eq {a b : EvmWord}
    (h_floor :
      (n4CallAddbackBeqQHatV4 a b).toNat =
        ((n4CallAddbackBeqU4 a b).toNat * 2^64 +
            (n4CallAddbackBeqU3 a b).toNat) /
          (n4CallAddbackBeqB3Prime b).toNat) :
    n4CallAddbackBeqQHatHighDivBound a b := by
  rw [n4CallAddbackBeqQHatHighDivBound_def,
    n4CallAddbackBeqHighDivVal_def]
  omega

theorem n4CallAddbackBeqQHatHighDivBound.floor_eq_of_call_rhatdd_hi_zero
    {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hcall : isCallTrialN4 (a.getLimbN 3) (b.getLimbN 2) (b.getLimbN 3))
    (h_rhat_hi_zero :
      divKTrialCallV4Rhatdd
          (n4CallAddbackBeqU4 a b)
          (n4CallAddbackBeqU3 a b)
          (n4CallAddbackBeqB3Prime b) >>> (32 : BitVec 6).toNat =
        (0 : Word))
    (h_qhat_high : n4CallAddbackBeqQHatHighDivBound a b) :
    (n4CallAddbackBeqQHatV4 a b).toNat = n4CallAddbackBeqHighDivVal a b := by
  rw [n4CallAddbackBeqHighDivVal_def]
  rw [n4CallAddbackBeqQHatHighDivBound_def,
    n4CallAddbackBeqHighDivVal_def] at h_qhat_high
  exact n4CallAddbackBeqQHatV4_eq_floor_of_call_rhatdd_hi_zero_of_le
    hb3nz hshift_nz hcall h_rhat_hi_zero h_qhat_high

/-- Runtime-bounds package from the named high-divisor qhat and Knuth-A
    bridge predicates. -/
theorem n4CallAddbackBeqRuntimeBounds_of_high_div_bounds_and_borrow
    {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (h_qhat_high : n4CallAddbackBeqQHatHighDivBound a b)
    (h_high_div : n4CallAddbackBeqHighDivKnuthABound a b)
    (h_borrow : isAddbackBorrowN4CallV4Evm a b) :
    n4CallAddbackBeqRuntimeBounds a b := by
  rw [n4CallAddbackBeqQHatHighDivBound_def,
    n4CallAddbackBeqHighDivVal_def] at h_qhat_high
  rw [n4CallAddbackBeqHighDivKnuthABound_def,
    n4CallAddbackBeqHighDivVal_def] at h_high_div
  exact n4CallAddbackBeqRuntimeBounds_of_qhat_bound_and_borrow
    hb3nz (le_trans h_qhat_high h_high_div) h_borrow

/-- Runtime semantic bridge from the named high-divisor qhat and Knuth-A
    bridge predicates. -/
theorem n4CallAddbackBeqSemanticHoldsV4_of_high_div_bounds_and_borrow
    {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (h_qhat_high : n4CallAddbackBeqQHatHighDivBound a b)
    (h_high_div : n4CallAddbackBeqHighDivKnuthABound a b)
    (h_borrow : isAddbackBorrowN4CallV4Evm a b)
    (h_carry2 : isAddbackCarry2NzN4CallV4Evm a b) :
    n4CallAddbackBeqSemanticHoldsV4 a b :=
  n4CallAddbackBeqSemanticHoldsV4_of_runtime_bounds
    hb3nz hshift_nz
    (n4CallAddbackBeqRuntimeBounds_of_high_div_bounds_and_borrow
      hb3nz h_qhat_high h_high_div h_borrow)
    h_borrow h_carry2

/-- Historical non-`V4` spelling of
    `n4CallAddbackBeqSemanticHoldsV4_of_high_div_bounds_and_borrow`. -/
theorem n4CallAddbackBeqSemanticHolds_of_high_div_bounds_and_borrow
    {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (h_qhat_high : n4CallAddbackBeqQHatHighDivBound a b)
    (h_high_div : n4CallAddbackBeqHighDivKnuthABound a b)
    (h_borrow : isAddbackBorrowN4CallV4Evm a b)
    (h_carry2 : isAddbackCarry2NzN4CallV4Evm a b) :
    n4CallAddbackBeqSemanticHolds a b := by
  simpa [n4CallAddbackBeqSemanticHolds_eq_v4] using
    n4CallAddbackBeqSemanticHoldsV4_of_high_div_bounds_and_borrow
      hb3nz hshift_nz h_qhat_high h_high_div h_borrow h_carry2

/-- Runtime-bounds package from exact-floor qhat evidence and the named
    Knuth-A high-divisor bridge. -/
theorem n4CallAddbackBeqRuntimeBounds_of_floor_eq_high_div_bound_and_borrow
    {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (h_floor :
      (n4CallAddbackBeqQHatV4 a b).toNat =
        ((n4CallAddbackBeqU4 a b).toNat * 2^64 +
            (n4CallAddbackBeqU3 a b).toNat) /
          (n4CallAddbackBeqB3Prime b).toNat)
    (h_high_div : n4CallAddbackBeqHighDivKnuthABound a b)
    (h_borrow : isAddbackBorrowN4CallV4Evm a b) :
    n4CallAddbackBeqRuntimeBounds a b :=
  n4CallAddbackBeqRuntimeBounds_of_high_div_bounds_and_borrow
    hb3nz
    (n4CallAddbackBeqQHatHighDivBound.of_floor_eq h_floor)
    h_high_div
    h_borrow

/-- Runtime semantic bridge from exact-floor qhat evidence and the named
    Knuth-A high-divisor bridge. -/
theorem n4CallAddbackBeqSemanticHoldsV4_of_floor_eq_high_div_bound_and_borrow
    {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (h_floor :
      (n4CallAddbackBeqQHatV4 a b).toNat =
        ((n4CallAddbackBeqU4 a b).toNat * 2^64 +
            (n4CallAddbackBeqU3 a b).toNat) /
          (n4CallAddbackBeqB3Prime b).toNat)
    (h_high_div : n4CallAddbackBeqHighDivKnuthABound a b)
    (h_borrow : isAddbackBorrowN4CallV4Evm a b)
    (h_carry2 : isAddbackCarry2NzN4CallV4Evm a b) :
    n4CallAddbackBeqSemanticHoldsV4 a b :=
  n4CallAddbackBeqSemanticHoldsV4_of_high_div_bounds_and_borrow
    hb3nz hshift_nz
    (n4CallAddbackBeqQHatHighDivBound.of_floor_eq h_floor)
    h_high_div
    h_borrow h_carry2

/-- Historical non-`V4` spelling of
    `n4CallAddbackBeqSemanticHoldsV4_of_floor_eq_high_div_bound_and_borrow`. -/
theorem n4CallAddbackBeqSemanticHolds_of_floor_eq_high_div_bound_and_borrow
    {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (h_floor :
      (n4CallAddbackBeqQHatV4 a b).toNat =
        ((n4CallAddbackBeqU4 a b).toNat * 2^64 +
            (n4CallAddbackBeqU3 a b).toNat) /
          (n4CallAddbackBeqB3Prime b).toNat)
    (h_high_div : n4CallAddbackBeqHighDivKnuthABound a b)
    (h_borrow : isAddbackBorrowN4CallV4Evm a b)
    (h_carry2 : isAddbackCarry2NzN4CallV4Evm a b) :
    n4CallAddbackBeqSemanticHolds a b := by
  simpa [n4CallAddbackBeqSemanticHolds_eq_v4] using
    n4CallAddbackBeqSemanticHoldsV4_of_floor_eq_high_div_bound_and_borrow
      hb3nz hshift_nz h_floor h_high_div h_borrow h_carry2

/-- Runtime-bounds package from the call-path exact-floor bridge and the
    named Knuth-A high-divisor bridge. -/
theorem n4CallAddbackBeqRuntimeBounds_of_call_high_div_bound_and_borrow
    {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hcall : isCallTrialN4 (a.getLimbN 3) (b.getLimbN 2) (b.getLimbN 3))
    (h_rhat_hi_zero :
      divKTrialCallV4Rhatdd
          (n4CallAddbackBeqU4 a b)
          (n4CallAddbackBeqU3 a b)
          (n4CallAddbackBeqB3Prime b) >>> (32 : BitVec 6).toNat =
        (0 : Word))
    (h_qhat_high : n4CallAddbackBeqQHatHighDivBound a b)
    (h_high_div : n4CallAddbackBeqHighDivKnuthABound a b)
    (h_borrow : isAddbackBorrowN4CallV4Evm a b) :
    n4CallAddbackBeqRuntimeBounds a b :=
  n4CallAddbackBeqRuntimeBounds_of_floor_eq_high_div_bound_and_borrow
    hb3nz
    (by
      simpa [n4CallAddbackBeqHighDivVal_def] using
        n4CallAddbackBeqQHatHighDivBound.floor_eq_of_call_rhatdd_hi_zero
          hb3nz hshift_nz hcall h_rhat_hi_zero h_qhat_high)
    h_high_div h_borrow

/-- Runtime semantic bridge from the call-path exact-floor bridge and the
    named Knuth-A high-divisor bridge. -/
theorem n4CallAddbackBeqSemanticHoldsV4_of_call_high_div_bound_and_borrow
    {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hcall : isCallTrialN4 (a.getLimbN 3) (b.getLimbN 2) (b.getLimbN 3))
    (h_rhat_hi_zero :
      divKTrialCallV4Rhatdd
          (n4CallAddbackBeqU4 a b)
          (n4CallAddbackBeqU3 a b)
          (n4CallAddbackBeqB3Prime b) >>> (32 : BitVec 6).toNat =
        (0 : Word))
    (h_qhat_high : n4CallAddbackBeqQHatHighDivBound a b)
    (h_high_div : n4CallAddbackBeqHighDivKnuthABound a b)
    (h_borrow : isAddbackBorrowN4CallV4Evm a b)
    (h_carry2 : isAddbackCarry2NzN4CallV4Evm a b) :
    n4CallAddbackBeqSemanticHoldsV4 a b :=
  n4CallAddbackBeqSemanticHoldsV4_of_floor_eq_high_div_bound_and_borrow
    hb3nz hshift_nz
    (by
      simpa [n4CallAddbackBeqHighDivVal_def] using
        n4CallAddbackBeqQHatHighDivBound.floor_eq_of_call_rhatdd_hi_zero
          hb3nz hshift_nz hcall h_rhat_hi_zero h_qhat_high)
    h_high_div h_borrow h_carry2

/-- Historical non-`V4` spelling of
    `n4CallAddbackBeqSemanticHoldsV4_of_call_high_div_bound_and_borrow`. -/
theorem n4CallAddbackBeqSemanticHolds_of_call_high_div_bound_and_borrow
    {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hcall : isCallTrialN4 (a.getLimbN 3) (b.getLimbN 2) (b.getLimbN 3))
    (h_rhat_hi_zero :
      divKTrialCallV4Rhatdd
          (n4CallAddbackBeqU4 a b)
          (n4CallAddbackBeqU3 a b)
          (n4CallAddbackBeqB3Prime b) >>> (32 : BitVec 6).toNat =
        (0 : Word))
    (h_qhat_high : n4CallAddbackBeqQHatHighDivBound a b)
    (h_high_div : n4CallAddbackBeqHighDivKnuthABound a b)
    (h_borrow : isAddbackBorrowN4CallV4Evm a b)
    (h_carry2 : isAddbackCarry2NzN4CallV4Evm a b) :
    n4CallAddbackBeqSemanticHolds a b := by
  simpa [n4CallAddbackBeqSemanticHolds_eq_v4] using
    n4CallAddbackBeqSemanticHoldsV4_of_call_high_div_bound_and_borrow
      hb3nz hshift_nz hcall h_rhat_hi_zero h_qhat_high h_high_div h_borrow h_carry2

/-- Runtime-bounds package from a direct qhat high-divisor bound, the weakened
    Knuth-A `+1` denominator bridge, and the runtime borrow predicate. -/
theorem n4CallAddbackBeqRuntimeBounds_of_qhat_high_div_le_norm_plus_one_and_borrow
    {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (h_qhat_le_high_div :
      (n4CallAddbackBeqQHatV4 a b).toNat ≤
        ((n4CallAddbackBeqU4 a b).toNat * 2^64 +
            (n4CallAddbackBeqU3 a b).toNat) /
          (n4CallAddbackBeqB3Prime b).toNat)
    (h_high_div_le_norm_plus_one :
      ((n4CallAddbackBeqU4 a b).toNat * 2^64 +
          (n4CallAddbackBeqU3 a b).toNat) /
        (n4CallAddbackBeqB3Prime b).toNat ≤
          n4CallAddbackBeqULoNormVal a b / n4CallAddbackBeqBNormVal b + 1)
    (h_borrow : isAddbackBorrowN4CallV4Evm a b) :
    n4CallAddbackBeqRuntimeBounds a b :=
  n4CallAddbackBeqRuntimeBounds_of_high_div_bounds_and_borrow
    hb3nz
    (n4CallAddbackBeqQHatHighDivBound.of_le h_qhat_le_high_div)
    (n4CallAddbackBeqHighDivKnuthABound.of_le h_high_div_le_norm_plus_one)
    h_borrow

/-- Runtime semantic bridge from a direct qhat high-divisor bound and the
    weakened Knuth-A `+1` denominator bridge. -/
theorem n4CallAddbackBeqSemanticHoldsV4_of_qhat_high_div_le_norm_plus_one_and_borrow
    {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (h_qhat_le_high_div :
      (n4CallAddbackBeqQHatV4 a b).toNat ≤
        ((n4CallAddbackBeqU4 a b).toNat * 2^64 +
            (n4CallAddbackBeqU3 a b).toNat) /
          (n4CallAddbackBeqB3Prime b).toNat)
    (h_high_div_le_norm_plus_one :
      ((n4CallAddbackBeqU4 a b).toNat * 2^64 +
          (n4CallAddbackBeqU3 a b).toNat) /
        (n4CallAddbackBeqB3Prime b).toNat ≤
          n4CallAddbackBeqULoNormVal a b / n4CallAddbackBeqBNormVal b + 1)
    (h_borrow : isAddbackBorrowN4CallV4Evm a b)
    (h_carry2 : isAddbackCarry2NzN4CallV4Evm a b) :
    n4CallAddbackBeqSemanticHoldsV4 a b :=
  n4CallAddbackBeqSemanticHoldsV4_of_runtime_bounds
    hb3nz hshift_nz
    (n4CallAddbackBeqRuntimeBounds_of_qhat_high_div_le_norm_plus_one_and_borrow
      hb3nz h_qhat_le_high_div h_high_div_le_norm_plus_one h_borrow)
    h_borrow h_carry2

/-- Historical non-`V4` spelling of
    `n4CallAddbackBeqSemanticHoldsV4_of_qhat_high_div_le_norm_plus_one_and_borrow`. -/
theorem n4CallAddbackBeqSemanticHolds_of_qhat_high_div_le_norm_plus_one_and_borrow
    {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (h_qhat_le_high_div :
      (n4CallAddbackBeqQHatV4 a b).toNat ≤
        ((n4CallAddbackBeqU4 a b).toNat * 2^64 +
            (n4CallAddbackBeqU3 a b).toNat) /
          (n4CallAddbackBeqB3Prime b).toNat)
    (h_high_div_le_norm_plus_one :
      ((n4CallAddbackBeqU4 a b).toNat * 2^64 +
          (n4CallAddbackBeqU3 a b).toNat) /
        (n4CallAddbackBeqB3Prime b).toNat ≤
          n4CallAddbackBeqULoNormVal a b / n4CallAddbackBeqBNormVal b + 1)
    (h_borrow : isAddbackBorrowN4CallV4Evm a b)
    (h_carry2 : isAddbackCarry2NzN4CallV4Evm a b) :
    n4CallAddbackBeqSemanticHolds a b := by
  simpa [n4CallAddbackBeqSemanticHolds_eq_v4] using
    n4CallAddbackBeqSemanticHoldsV4_of_qhat_high_div_le_norm_plus_one_and_borrow
      hb3nz hshift_nz h_qhat_le_high_div h_high_div_le_norm_plus_one h_borrow h_carry2

end EvmWord

end EvmAsm.Evm64
