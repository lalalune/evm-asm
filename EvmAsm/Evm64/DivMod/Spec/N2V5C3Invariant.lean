/-
  EvmAsm.Evm64.DivMod.Spec.N2V5C3Invariant

  Abstract (qHat-as-value) `c3 = 1` invariant from the `+2` overestimate and the
  unreachability of the `c3 ∈ {0, 2}` frontier under `carry = 0`.  This is the
  raw `hc3` form that `callAddbackCarry2NzV5_of_overestimate_c3` (#7424)
  consumes, with `q := divKTrialCallV5QHat u2 u1 v1`.

  It is the qHat-abstract generalization of
  `MulsubBltC3OneOfCarryZero_of_plus_two_and_unreach`
  (DivBltC3InvariantPlusTwoCase, which is hardcoded to `divKTrialCallV4QHat`):
  the proof is purely structural over `mulsubN4 q …` (only `mulsubN4_c3_le_two`
  uses `hq_over`), so it applies verbatim to the v5 trial.  Feed `hq_over` from
  `divKTrialCallV5QHat_le_window_div_plus_two_of_call` (#7425).
-/

import EvmAsm.Evm64.EvmWordArith.DivMulsubC3LeTwo

namespace EvmAsm.Evm64

open EvmWord EvmAsm.Rv64

/-- `c3 = 1` (in raw `carry = 0 → c3 = 1` form) for an arbitrary trial value `q`,
    from the `+2` overestimate of `q` and the unreachability of the
    `c3 = 0` / `c3 = 2` cases under `carry = 0`. -/
theorem mulsubN4_c3_one_of_carry_zero_of_plus_two_and_unreach
    (q v0 v1 v2 v3 u0 u1 u2 u3 : Word)
    (hbnz : v0 ||| v1 ||| v2 ||| v3 ≠ 0)
    (hq_over : q.toNat ≤ val256 u0 u1 u2 u3 / val256 v0 v1 v2 v3 + 2)
    (h_unreach0 :
      ¬ (addbackN4_carry
            (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).1
            (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.1
            (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.1
            (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.1
            v0 v1 v2 v3 = 0 ∧
          (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2 = 0))
    (h_unreach2 :
      ¬ (addbackN4_carry
            (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).1
            (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.1
            (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.1
            (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.1
            v0 v1 v2 v3 = 0 ∧
          (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2.toNat = 2)) :
    addbackN4_carry
        (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).1
        (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.1
        (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.1
        (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.1
        v0 v1 v2 v3 = 0 →
      (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2 = 1 := by
  intro h_carry_zero
  have h_c3_le_two := mulsubN4_c3_le_two hbnz hq_over
  apply BitVec.eq_of_toNat_eq
  rcases Nat.lt_or_ge (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2.toNat 1 with h_lt1 | h_ge1
  · exfalso
    have h_c3_zero : (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2 = 0 := by
      apply BitVec.eq_of_toNat_eq
      have h_zero : (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2.toNat = 0 := by omega
      rw [h_zero]; rfl
    exact h_unreach0 ⟨h_carry_zero, h_c3_zero⟩
  · rcases Nat.lt_or_ge (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2.toNat 2 with h_lt2 | h_ge2
    · have h_eq : (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2.toNat = 1 := by omega
      rw [h_eq]; rfl
    · exfalso
      have h_c3_two : (mulsubN4 q v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2.toNat = 2 := by omega
      exact h_unreach2 ⟨h_carry_zero, h_c3_two⟩

end EvmAsm.Evm64
