/-
  EvmAsm.Evm64.DivMod.Spec.DivisorFullDomainShape

  Full-domain Or-shape disjunction for `EvmWord`: every divisor falls into
  exactly one of five cases (bzero, n1, n2, n3, n4). Complements
  `nonzero_divisor_limb_shape` (PR #6972) with the bzero case included.
-/

import EvmAsm.Evm64.DivMod.Spec.DivisorLimbCaseHelpers

namespace EvmAsm.Evm64

open EvmAsm.Rv64 EvmWord

/-- Every divisor `b : EvmWord` falls into exactly one of five disjoint
    shape cases: `b = 0`, n1 (only limb 0 nonzero), n2 (limb 1 highest
    nonzero), n3 (limb 2 highest nonzero), n4 (limb 3 nonzero). -/
theorem divisor_full_domain_shape (b : EvmWord) :
    b = 0 ∨
    (b ≠ 0 ∧ b.getLimbN 3 = 0 ∧ b.getLimbN 2 = 0 ∧ b.getLimbN 1 = 0 ∧ b.getLimbN 0 ≠ 0) ∨
    (b ≠ 0 ∧ b.getLimbN 3 = 0 ∧ b.getLimbN 2 = 0 ∧ b.getLimbN 1 ≠ 0) ∨
    (b ≠ 0 ∧ b.getLimbN 3 = 0 ∧ b.getLimbN 2 ≠ 0) ∨
    (b ≠ 0 ∧ b.getLimbN 3 ≠ 0) := by
  by_cases hbz : b = 0
  · left; exact hbz
  · rcases nonzero_divisor_limb_shape b hbz with
      ⟨hb3z, hb2z, hb1z, hb0nz⟩ | ⟨hb3z, hb2z, hb1nz⟩ | ⟨hb3z, hb2nz⟩ | hb3nz
    · right; left; exact ⟨hbz, hb3z, hb2z, hb1z, hb0nz⟩
    · right; right; left; exact ⟨hbz, hb3z, hb2z, hb1nz⟩
    · right; right; right; left; exact ⟨hbz, hb3z, hb2nz⟩
    · right; right; right; right; exact ⟨hbz, hb3nz⟩

end EvmAsm.Evm64
