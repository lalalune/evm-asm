/-
  EvmAsm.Evm64.DivMod.Spec.CallAddbackRuntimeHighDiv

  Small N4 call-addback runtime bridge lemmas that keep
  CallAddbackRuntime.lean below the file-size guardrail.
-/

import EvmAsm.Evm64.DivMod.Spec.CallAddbackRuntime

namespace EvmAsm.Evm64

namespace EvmWord

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
  n4CallAddbackBeqRuntimeBounds_of_qhat_bound_and_borrow
    hb3nz
    (le_trans h_qhat_le_high_div h_high_div_le_norm_plus_one)
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
