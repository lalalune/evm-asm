/-
  EvmAsm.Evm64.DivMod.Spec.N2V5CallCarryFromUnreach

  Compose the call-digit carry helper (#7424,
  `callAddbackCarry2NzV5_of_overestimate_c3`) with the abstract `c3 = 1`
  invariant (#7426, `mulsubN4_c3_one_of_carry_zero_of_plus_two_and_unreach`):
  `callAddbackCarry2NzV5` from the `+2` overestimate plus the unreachability of
  the `c3 ∈ {0, 2}` frontier under `carry = 0`.  This reduces the call-digit
  carry to exactly the two unreach conditions (the last remaining shape-discharge
  for the call branch); the `+2` overestimate itself comes from
  `divKTrialCallV5QHat_le_window_div_plus_two_of_call` (#7425) in the call regime.
-/

import EvmAsm.Evm64.DivMod.Spec.N2V5CallAddbackOverestimate
import EvmAsm.Evm64.DivMod.Spec.N2V5C3Invariant

namespace EvmAsm.Evm64

open EvmWord EvmAsm.Rv64

/-- `callAddbackCarry2NzV5` from the `+2` overestimate and the unreachability of
    the `c3 = 0` / `c3 = 2` cases under `carry = 0`. -/
theorem callAddbackCarry2NzV5_of_overestimate_and_unreach
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word)
    (hbnz : v0 ||| v1 ||| v2 ||| v3 ≠ 0)
    (hq_over : (divKTrialCallV5QHat u2 u1 v1).toNat ≤
      val256 u0 u1 u2 u3 / val256 v0 v1 v2 v3 + 2)
    (h_unreach0 :
      ¬ (addbackN4_carry
            (mulsubN4 (divKTrialCallV5QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3).1
            (mulsubN4 (divKTrialCallV5QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3).2.1
            (mulsubN4 (divKTrialCallV5QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3).2.2.1
            (mulsubN4 (divKTrialCallV5QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.1
            v0 v1 v2 v3 = 0 ∧
          (mulsubN4 (divKTrialCallV5QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2 = 0))
    (h_unreach2 :
      ¬ (addbackN4_carry
            (mulsubN4 (divKTrialCallV5QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3).1
            (mulsubN4 (divKTrialCallV5QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3).2.1
            (mulsubN4 (divKTrialCallV5QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3).2.2.1
            (mulsubN4 (divKTrialCallV5QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.1
            v0 v1 v2 v3 = 0 ∧
          (mulsubN4 (divKTrialCallV5QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2.toNat = 2)) :
    callAddbackCarry2NzV5 v0 v1 v2 v3 u0 u1 u2 u3 uTop :=
  callAddbackCarry2NzV5_of_overestimate_c3 v0 v1 v2 v3 u0 u1 u2 u3 uTop hbnz hq_over
    (mulsubN4_c3_one_of_carry_zero_of_plus_two_and_unreach
      (divKTrialCallV5QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3 hbnz hq_over h_unreach0 h_unreach2)

end EvmAsm.Evm64
