/-
  EvmAsm.Evm64.DivMod.Spec.N2V5RemainderLt

  The v5 n=2 per-digit remainder bound, assembled from the abstract toolkit:
  `iterN2V5 true` (the call path) leaves a remainder `< val256 v`.

  This feeds the unified `iterWithDoubleAddback_remainder_lt_of_plus_two` (#7346)
  with the four discharged inputs:
  - `hbnz` from the divisor shape;
  - `hc3_one_of_borrow` from `mulsubN4_c3_eq_one_v3_zero` (the 2-limb divisor has
    `v3 = 0`, so any borrow carry is exactly 1);
  - `hq_over` (`+2`) from `n2_window_div_le_val256_div_plus_two_v5` (#7349);
  - `hq_ge` (no-underestimate) from `n2_window_val256_div_le_trial_v5` (#7347),
    converted to the `< (q+1)·val256 v` form via `Nat.div_lt_iff_lt_mul`.

  The call regime (`u2 < v1`) and normalization (`v1 ≥ 2^63`) are supplied by the
  loop invariant / divisor shape.  This is the per-digit remainder fact that
  collapses each intermediate remainder to its low two limbs for the n=2
  telescope (`fullDivN2V5_three_step_nat`, #7344).  Bead `evm-asm-wbc4i.9.2`.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN2V5Families
import EvmAsm.Evm64.EvmWordArith.DivN4RemainderLt
import EvmAsm.Evm64.EvmWordArith.KnuthAFloorWindow

namespace EvmAsm.Evm64

open EvmWord EvmAsm.Rv64

/-- **v5 n=2 per-digit remainder bound (call path).** For a normalized 2-limb
    divisor (`v1 ≥ 2^63`) in the call regime (`u2 < v1`), the `iterN2V5 true`
    iteration leaves a remainder `< val256 v`.  Assembled from the abstract
    `iterWithDoubleAddback_remainder_lt_of_plus_two` with the trial bracket
    (#7347 lower, #7349 upper) and the `v3 = 0` borrow-carry fact. -/
theorem iterN2V5_true_remainder_lt
    (v0 v1 u0 u1 u2 : Word)
    (hbnz : v0 ||| v1 ||| 0 ||| 0 ≠ 0)
    (hv1 : v1.toNat ≥ 2^63)
    (hcall : u2.toNat < v1.toNat) :
    EvmWord.val256
        (iterN2V5 true v0 v1 0 0 u0 u1 u2 0 0).2.1
        (iterN2V5 true v0 v1 0 0 u0 u1 u2 0 0).2.2.1
        (iterN2V5 true v0 v1 0 0 u0 u1 u2 0 0).2.2.2.1
        (iterN2V5 true v0 v1 0 0 u0 u1 u2 0 0).2.2.2.2.1 +
      (iterN2V5 true v0 v1 0 0 u0 u1 u2 0 0).2.2.2.2.2.toNat * 2^256 <
    EvmWord.val256 v0 v1 0 0 := by
  have hrw : iterN2V5 true v0 v1 0 0 u0 u1 u2 0 0 =
      iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1) v0 v1 0 0 u0 u1 u2 0 0 := by
    unfold iterN2V5; rw [if_pos rfl]
  rw [hrw]
  have hv_pos : 0 < val256 v0 v1 0 0 := by
    have h0 : (0 : Word).toNat = 0 := rfl
    simp only [EvmWord.val256, h0]; omega
  have hq_over := n2_window_div_le_val256_div_plus_two_v5 v0 v1 u0 u1 u2 hv1 hcall
  have hge := n2_window_val256_div_le_trial_v5 v0 v1 u0 u1 u2 hv1 hcall
  have hq_ge : val256 u0 u1 u2 0 + (0 : Word).toNat * 2^256 <
      ((divKTrialCallV5QHat u2 u1 v1).toNat + 1) * val256 v0 v1 0 0 := by
    have h0 : (0 : Word).toNat = 0 := rfl
    rw [h0, Nat.zero_mul, Nat.add_zero]
    exact (Nat.div_lt_iff_lt_mul hv_pos).mp (by omega)
  have hc3 : BitVec.ult (0 : Word)
        (mulsubN4 (divKTrialCallV5QHat u2 u1 v1) v0 v1 0 0 u0 u1 u2 0).2.2.2.2 →
      (mulsubN4 (divKTrialCallV5QHat u2 u1 v1) v0 v1 0 0 u0 u1 u2 0).2.2.2.2 = 1 := by
    intro hb
    apply mulsubN4_c3_eq_one_v3_zero
    intro h0
    rw [h0] at hb
    exact absurd hb (by decide)
  exact iterWithDoubleAddback_remainder_lt_of_plus_two
    (divKTrialCallV5QHat u2 u1 v1) v0 v1 0 0 u0 u1 u2 0 0 hbnz hc3 hq_over hq_ge

end EvmAsm.Evm64
