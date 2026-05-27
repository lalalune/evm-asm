/-
  EvmAsm.Evm64.DivMod.Spec.DivisorLimbCaseShapeBridge

  Bridge from the `DivisorLimbCase` inductive (with five constructors carrying
  full shape facts) to the Prop disjunction `divisor_full_domain_shape`.

  Useful when downstream code wants to consume the `DivisorLimbCase` via a
  flat disjunction without pattern matching on the inductive.
-/

import EvmAsm.Evm64.DivMod.Spec.DivisorFullDomainShape

namespace EvmAsm.Evm64

open EvmAsm.Rv64 EvmWord

/-- Convert any `DivisorLimbCase b` into the corresponding flat
    full-domain shape disjunction. -/
theorem divisor_full_domain_shape_of_DivisorLimbCase
    {b : EvmWord} (h : DivisorLimbCase b) :
    b = 0 ∨
    (b ≠ 0 ∧ b.getLimbN 3 = 0 ∧ b.getLimbN 2 = 0 ∧ b.getLimbN 1 = 0 ∧ b.getLimbN 0 ≠ 0) ∨
    (b ≠ 0 ∧ b.getLimbN 3 = 0 ∧ b.getLimbN 2 = 0 ∧ b.getLimbN 1 ≠ 0) ∨
    (b ≠ 0 ∧ b.getLimbN 3 = 0 ∧ b.getLimbN 2 ≠ 0) ∨
    (b ≠ 0 ∧ b.getLimbN 3 ≠ 0) := by
  cases h with
  | bzero hbz => left; exact hbz
  | n1 hbnz _ hb3z hb2z hb1z hb0nz =>
      right; left; exact ⟨hbnz, hb3z, hb2z, hb1z, hb0nz⟩
  | n2 hbnz _ hb3z hb2z hb1nz =>
      right; right; left; exact ⟨hbnz, hb3z, hb2z, hb1nz⟩
  | n3 hbnz _ hb3z hb2nz =>
      right; right; right; left; exact ⟨hbnz, hb3z, hb2nz⟩
  | n4 hbnz _ hb3nz =>
      right; right; right; right; exact ⟨hbnz, hb3nz⟩

end EvmAsm.Evm64
