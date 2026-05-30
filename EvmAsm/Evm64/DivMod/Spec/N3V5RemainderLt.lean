/-
  EvmAsm.Evm64.DivMod.Spec.N3V5RemainderLt

  The v5 n=3 per-digit val256 conservation (call path).  For a 3-limb divisor
  `(v0,v1,v2,0)` (top limb `v2`, normalized `v2 ≥ 2^63`) in the call regime
  (`u3 < v2`), the digit's `iterWithDoubleAddback` over the v5 trial
  `divKTrialCallV5QHat u3 u2 v2` satisfies the Euclidean conservation

    `val256 u0 u1 u2 u3 + uTop·2^256
       = q·val256 v0 v1 v2 0 + val256(rem) + carry·2^256`.

  The n=3 analog of `iterN2V5_true_conservation_from_shape`, stated directly on
  `iterWithDoubleAddback` (the form `iterN3V5 true` unfolds to via
  `iterN3V5_unfold` + `if_pos`).  Reuses the position-independent
  `iterWithDoubleAddback_val256_conservation_of_branch_bounds` with the n=3 trial
  overestimate `n3_window_div_le_val256_div_plus_two_v5` (KnuthAFloorWindowN3) and
  `mulsubN4_c3_eq_one_v3_zero` (the `v3 = 0` borrow fact).  Per-digit step input
  for the v5 n=3 quotient telescope.  Bead `evm-asm-wbc4i.9.3`.
-/

import EvmAsm.Evm64.EvmWordArith.KnuthAFloorWindowN3
import EvmAsm.Evm64.EvmWordArith.DivN4Overestimate

namespace EvmAsm.Evm64

open EvmWord EvmAsm.Rv64

/-- **v5 n=3 per-digit val256 conservation (call path).**  `q = divKTrialCallV5QHat
    u3 u2 v2` is the v5 trial; the digit's double-addback iterate conserves value
    against the 3-limb divisor `(v0,v1,v2,0)`. -/
theorem n3_trial_call_val256_conservation
    (v0 v1 v2 u0 u1 u2 u3 uTop : Word)
    (hv2 : v2.toNat ≥ 2^63)
    (hcall : u3.toNat < v2.toNat) :
    val256 u0 u1 u2 u3 + uTop.toNat * 2 ^ 256 =
      (iterWithDoubleAddback (divKTrialCallV5QHat u3 u2 v2)
          v0 v1 v2 0 u0 u1 u2 u3 uTop).1.toNat * val256 v0 v1 v2 0 +
        val256
          (iterWithDoubleAddback (divKTrialCallV5QHat u3 u2 v2) v0 v1 v2 0 u0 u1 u2 u3 uTop).2.1
          (iterWithDoubleAddback (divKTrialCallV5QHat u3 u2 v2) v0 v1 v2 0 u0 u1 u2 u3 uTop).2.2.1
          (iterWithDoubleAddback (divKTrialCallV5QHat u3 u2 v2) v0 v1 v2 0 u0 u1 u2 u3 uTop).2.2.2.1
          (iterWithDoubleAddback (divKTrialCallV5QHat u3 u2 v2) v0 v1 v2 0 u0 u1 u2 u3 uTop).2.2.2.2.1 +
        (iterWithDoubleAddback (divKTrialCallV5QHat u3 u2 v2)
          v0 v1 v2 0 u0 u1 u2 u3 uTop).2.2.2.2.2.toNat * 2 ^ 256 := by
  have hbnz : v0 ||| v1 ||| v2 ||| 0 ≠ 0 := by
    intro h
    have hv2z : v2 = 0 := (BitVec.or_eq_zero_iff.mp (BitVec.or_eq_zero_iff.mp h).1).2
    rw [hv2z] at hv2; simp at hv2
  set q := divKTrialCallV5QHat u3 u2 v2 with hq
  have hq_over : q.toNat ≤ val256 u0 u1 u2 u3 / val256 v0 v1 v2 0 + 2 := by
    rw [hq]; exact n3_window_div_le_val256_div_plus_two_v5 v0 v1 v2 u0 u1 u2 u3 hv2 hcall
  have hc3 : BitVec.ult uTop (mulsubN4 q v0 v1 v2 0 u0 u1 u2 u3).2.2.2.2 →
      (mulsubN4 q v0 v1 v2 0 u0 u1 u2 u3).2.2.2.2 = 1 := by
    intro hb
    apply mulsubN4_c3_eq_one_v3_zero
    intro hc3z
    rw [hc3z] at hb
    exact absurd hb (by simp [BitVec.ult])
  exact iterWithDoubleAddback_val256_conservation_of_branch_bounds
    q v0 v1 v2 0 u0 u1 u2 u3 uTop hbnz hq_over hc3
    (fun hb _ => q_pos_of_mulsub_borrow q v0 v1 v2 0 u0 u1 u2 u3 (hc3 hb))
    (fun hb hcz => q_ge_two_of_mulsub_borrow_and_addback_carry_zero
      q v0 v1 v2 0 u0 u1 u2 u3 (hc3 hb) hcz)

end EvmAsm.Evm64
