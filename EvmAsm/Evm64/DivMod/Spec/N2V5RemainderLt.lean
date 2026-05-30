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
import EvmAsm.Evm64.EvmWordArith.DivN2MaxOverestimate

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

/-- The n=2 divisor value is a 2-limb number, hence `< 2^128`. -/
theorem n2_val256_v_lt_pow128 (v0 v1 : Word) : val256 v0 v1 0 0 < 2^128 := by
  have h0 : (0 : Word).toNat = 0 := rfl
  have := v0.isLt; have := v1.isLt
  simp only [EvmWord.val256, h0]; omega

/-- **v5 n=2 per-digit remainder collapse.** Since the remainder is `< val256 v
    < 2^128`, its two high limbs and the overflow cell are zero — so its `val256`
    occupies only the low two limbs.  Lets the per-digit conservation reduce to
    the 2-limb step form consumed by `fullDivN2V5_three_step_nat`. -/
theorem iterN2V5_true_remainder_collapse
    (v0 v1 u0 u1 u2 : Word)
    (hbnz : v0 ||| v1 ||| 0 ||| 0 ≠ 0)
    (hv1 : v1.toNat ≥ 2^63)
    (hcall : u2.toNat < v1.toNat) :
    (iterN2V5 true v0 v1 0 0 u0 u1 u2 0 0).2.2.2.1 = 0 ∧
    (iterN2V5 true v0 v1 0 0 u0 u1 u2 0 0).2.2.2.2.1 = 0 ∧
    (iterN2V5 true v0 v1 0 0 u0 u1 u2 0 0).2.2.2.2.2 = 0 := by
  have hlt := iterN2V5_true_remainder_lt v0 v1 u0 u1 u2 hbnz hv1 hcall
  have hv128 := n2_val256_v_lt_pow128 v0 v1
  set out := iterN2V5 true v0 v1 0 0 u0 u1 u2 0 0 with hout
  have key : val256 out.2.1 out.2.2.1 out.2.2.2.1 out.2.2.2.2.1 +
      out.2.2.2.2.2.toNat * 2^256 < 2^128 := by omega
  have hr2 := out.2.2.2.1.isLt
  have hr3 := out.2.2.2.2.1.isLt
  refine ⟨?_, ?_, ?_⟩
  · have : out.2.2.2.1.toNat = 0 := by simp only [EvmWord.val256] at key; omega
    exact BitVec.eq_of_toNat_eq (by rw [this]; rfl)
  · have : out.2.2.2.2.1.toNat = 0 := by simp only [EvmWord.val256] at key; omega
    exact BitVec.eq_of_toNat_eq (by rw [this]; rfl)
  · have : out.2.2.2.2.2.toNat = 0 := by simp only [EvmWord.val256] at key; omega
    exact BitVec.eq_of_toNat_eq (by rw [this]; rfl)

/-- **v5 n=2 per-digit conservation from shape (no `Carry2Nz`).** The call-path
    iteration preserves value: `val256 window = q·val256 v + val256(remainder) +
    overflow·2^256`, with `q` the output quotient digit.  Discharged purely from
    the trial bracket via `iterWithDoubleAddback_val256_conservation_of_branch_bounds`
    — needs NO `isAddbackCarry2Nz` hypothesis (the q-magnitude side conditions
    come from `q_pos_of_mulsub_borrow` / `q_ge_two_of_mulsub_borrow_and_addback_carry_zero`).
    This is the cleaner replacement for the `…_of_carry2`-based conservations. -/
theorem iterN2V5_true_conservation_from_shape
    (v0 v1 u0 u1 u2 : Word)
    (hbnz : v0 ||| v1 ||| 0 ||| 0 ≠ 0)
    (hv1 : v1.toNat ≥ 2^63)
    (hcall : u2.toNat < v1.toNat) :
    val256 u0 u1 u2 0 =
      (iterN2V5 true v0 v1 0 0 u0 u1 u2 0 0).1.toNat * val256 v0 v1 0 0 +
        val256
          (iterN2V5 true v0 v1 0 0 u0 u1 u2 0 0).2.1
          (iterN2V5 true v0 v1 0 0 u0 u1 u2 0 0).2.2.1
          (iterN2V5 true v0 v1 0 0 u0 u1 u2 0 0).2.2.2.1
          (iterN2V5 true v0 v1 0 0 u0 u1 u2 0 0).2.2.2.2.1 +
        (iterN2V5 true v0 v1 0 0 u0 u1 u2 0 0).2.2.2.2.2.toNat * 2^256 := by
  have hrw : iterN2V5 true v0 v1 0 0 u0 u1 u2 0 0 =
      iterWithDoubleAddback (divKTrialCallV5QHat u2 u1 v1) v0 v1 0 0 u0 u1 u2 0 0 := by
    unfold iterN2V5; rw [if_pos rfl]
  rw [hrw]
  set q := divKTrialCallV5QHat u2 u1 v1 with hq
  have hq_over := n2_window_div_le_val256_div_plus_two_v5 v0 v1 u0 u1 u2 hv1 hcall
  have hc3 : BitVec.ult (0 : Word) (mulsubN4 q v0 v1 0 0 u0 u1 u2 0).2.2.2.2 →
      (mulsubN4 q v0 v1 0 0 u0 u1 u2 0).2.2.2.2 = 1 := by
    intro hb
    apply mulsubN4_c3_eq_one_v3_zero
    intro h0; rw [h0] at hb; exact absurd hb (by decide)
  have hconv := iterWithDoubleAddback_val256_conservation_of_branch_bounds
    q v0 v1 0 0 u0 u1 u2 0 0 hbnz hq_over hc3
    (fun hb _ => q_pos_of_mulsub_borrow q v0 v1 0 0 u0 u1 u2 0 (hc3 hb))
    (fun hb hcz => q_ge_two_of_mulsub_borrow_and_addback_carry_zero
      q v0 v1 0 0 u0 u1 u2 0 (hc3 hb) hcz)
  have h0 : (0 : Word).toNat = 0 := rfl
  simpa [h0] using hconv

/-- **Combined clean 2-limb Euclidean step for the v5 n=2 call path.** From
    shape, `val256 window = q·val256 v + R` with `R = rem0 + 2^64·rem1 <
    val256 v` the collapsed 2-limb remainder.  Merges
    `iterN2V5_true_conservation_from_shape` with `iterN2V5_true_remainder_collapse`
    + `iterN2V5_true_remainder_lt` — exactly the per-digit step form fed to
    `fullDivN2V5_three_step_nat` (#7344) to assemble `fullDivN2MulSubEqV5`. -/
theorem iterN2V5_true_step
    (v0 v1 u0 u1 u2 : Word)
    (hbnz : v0 ||| v1 ||| 0 ||| 0 ≠ 0)
    (hv1 : v1.toNat ≥ 2^63)
    (hcall : u2.toNat < v1.toNat) :
    val256 u0 u1 u2 0 =
      (iterN2V5 true v0 v1 0 0 u0 u1 u2 0 0).1.toNat * val256 v0 v1 0 0 +
        ((iterN2V5 true v0 v1 0 0 u0 u1 u2 0 0).2.1.toNat +
          2^64 * (iterN2V5 true v0 v1 0 0 u0 u1 u2 0 0).2.2.1.toNat) ∧
      (iterN2V5 true v0 v1 0 0 u0 u1 u2 0 0).2.1.toNat +
          2^64 * (iterN2V5 true v0 v1 0 0 u0 u1 u2 0 0).2.2.1.toNat <
        val256 v0 v1 0 0 := by
  obtain ⟨hc2, hc3, hco⟩ := iterN2V5_true_remainder_collapse v0 v1 u0 u1 u2 hbnz hv1 hcall
  have hconv := iterN2V5_true_conservation_from_shape v0 v1 u0 u1 u2 hbnz hv1 hcall
  have hlt := iterN2V5_true_remainder_lt v0 v1 u0 u1 u2 hbnz hv1 hcall
  set out := iterN2V5 true v0 v1 0 0 u0 u1 u2 0 0 with hout
  have h0 : (0 : Word).toNat = 0 := rfl
  have hcollapse : val256 out.2.1 out.2.2.1 out.2.2.2.1 out.2.2.2.2.1 =
      out.2.1.toNat + 2^64 * out.2.2.1.toNat := by
    rw [hc2, hc3]; simp only [EvmWord.val256, h0]; ring
  constructor
  · rw [hconv, hcollapse, hco, h0]; ring
  · rw [hcollapse] at hlt; rw [hco, h0] at hlt; simpa using hlt

/-! ### Max branch (`bltu = false`)

The max path (`u2 ≥ v1`, trial `= 2^64-1`) mirrors the call path, with the
overestimate from `max_trial_local_overestimate_n2_of_not_ult` and the
no-underestimate `hq_ge` from the window-validity invariant
`val256 window < 2^64·val256 v` (since the max trial `+1 = 2^64`). -/

/-- **v5 n=2 per-digit remainder bound (max path).** -/
theorem iterN2V5_false_remainder_lt
    (v0 v1 u0 u1 u2 : Word) (hbnz : v0 ||| v1 ||| 0 ||| 0 ≠ 0)
    (hv1 : v1.toNat ≥ 2^63) (hbltu : ¬ BitVec.ult u2 v1)
    (hvalid : val256 u0 u1 u2 0 < 2^64 * val256 v0 v1 0 0) :
    EvmWord.val256 (iterN2V5 false v0 v1 0 0 u0 u1 u2 0 0).2.1
        (iterN2V5 false v0 v1 0 0 u0 u1 u2 0 0).2.2.1
        (iterN2V5 false v0 v1 0 0 u0 u1 u2 0 0).2.2.2.1
        (iterN2V5 false v0 v1 0 0 u0 u1 u2 0 0).2.2.2.2.1 +
      (iterN2V5 false v0 v1 0 0 u0 u1 u2 0 0).2.2.2.2.2.toNat * 2^256 <
    EvmWord.val256 v0 v1 0 0 := by
  have hrw : iterN2V5 false v0 v1 0 0 u0 u1 u2 0 0 =
      iterWithDoubleAddback (signExtend12 4095) v0 v1 0 0 u0 u1 u2 0 0 := by
    unfold iterN2V5 iterN2Max; simp only [Bool.false_eq_true, if_false]
  rw [hrw]
  set q : Word := signExtend12 4095 with hq
  have hq_over := max_trial_local_overestimate_n2_of_not_ult v0 v1 u0 u1 u2 hv1 hbltu
  have hqsucc : q.toNat + 1 = 2^64 := by rw [hq, signExtend12_4095_toNat]; omega
  have hq_ge : val256 u0 u1 u2 0 + (0 : Word).toNat * 2^256 < (q.toNat + 1) * val256 v0 v1 0 0 := by
    have h0 : (0 : Word).toNat = 0 := rfl
    rw [h0, hqsucc, Nat.zero_mul, Nat.add_zero]; exact hvalid
  have hc3 : BitVec.ult (0 : Word) (mulsubN4 q v0 v1 0 0 u0 u1 u2 0).2.2.2.2 →
      (mulsubN4 q v0 v1 0 0 u0 u1 u2 0).2.2.2.2 = 1 := by
    intro hb; apply mulsubN4_c3_eq_one_v3_zero; intro hz; rw [hz] at hb; exact absurd hb (by decide)
  exact iterWithDoubleAddback_remainder_lt_of_plus_two q v0 v1 0 0 u0 u1 u2 0 0 hbnz hc3 hq_over hq_ge

/-- **v5 n=2 per-digit conservation (max path).** -/
theorem iterN2V5_false_conservation
    (v0 v1 u0 u1 u2 : Word) (hbnz : v0 ||| v1 ||| 0 ||| 0 ≠ 0)
    (hv1 : v1.toNat ≥ 2^63) (hbltu : ¬ BitVec.ult u2 v1) :
    val256 u0 u1 u2 0 =
      (iterN2V5 false v0 v1 0 0 u0 u1 u2 0 0).1.toNat * val256 v0 v1 0 0 +
        val256 (iterN2V5 false v0 v1 0 0 u0 u1 u2 0 0).2.1
          (iterN2V5 false v0 v1 0 0 u0 u1 u2 0 0).2.2.1
          (iterN2V5 false v0 v1 0 0 u0 u1 u2 0 0).2.2.2.1
          (iterN2V5 false v0 v1 0 0 u0 u1 u2 0 0).2.2.2.2.1 +
        (iterN2V5 false v0 v1 0 0 u0 u1 u2 0 0).2.2.2.2.2.toNat * 2^256 := by
  have hrw : iterN2V5 false v0 v1 0 0 u0 u1 u2 0 0 =
      iterWithDoubleAddback (signExtend12 4095) v0 v1 0 0 u0 u1 u2 0 0 := by
    unfold iterN2V5 iterN2Max; simp only [Bool.false_eq_true, if_false]
  rw [hrw]
  set q : Word := signExtend12 4095 with hq
  have hq_over := max_trial_local_overestimate_n2_of_not_ult v0 v1 u0 u1 u2 hv1 hbltu
  have hq1 : 1 ≤ q.toNat := by rw [hq, signExtend12_4095_toNat]; omega
  have hq2 : 2 ≤ q.toNat := by rw [hq, signExtend12_4095_toNat]; omega
  have hc3 : BitVec.ult (0 : Word) (mulsubN4 q v0 v1 0 0 u0 u1 u2 0).2.2.2.2 →
      (mulsubN4 q v0 v1 0 0 u0 u1 u2 0).2.2.2.2 = 1 := by
    intro hb; apply mulsubN4_c3_eq_one_v3_zero; intro hz; rw [hz] at hb; exact absurd hb (by decide)
  have hconv := iterWithDoubleAddback_val256_conservation_of_branch_bounds
    q v0 v1 0 0 u0 u1 u2 0 0 hbnz hq_over hc3 (fun _ _ => hq1) (fun _ _ => hq2)
  have h0 : (0 : Word).toNat = 0 := rfl
  simpa [h0] using hconv

/-- **v5 n=2 per-digit remainder collapse (max path).** -/
theorem iterN2V5_false_remainder_collapse
    (v0 v1 u0 u1 u2 : Word) (hbnz : v0 ||| v1 ||| 0 ||| 0 ≠ 0)
    (hv1 : v1.toNat ≥ 2^63) (hbltu : ¬ BitVec.ult u2 v1)
    (hvalid : val256 u0 u1 u2 0 < 2^64 * val256 v0 v1 0 0) :
    (iterN2V5 false v0 v1 0 0 u0 u1 u2 0 0).2.2.2.1 = 0 ∧
    (iterN2V5 false v0 v1 0 0 u0 u1 u2 0 0).2.2.2.2.1 = 0 ∧
    (iterN2V5 false v0 v1 0 0 u0 u1 u2 0 0).2.2.2.2.2 = 0 := by
  have hlt := iterN2V5_false_remainder_lt v0 v1 u0 u1 u2 hbnz hv1 hbltu hvalid
  have hv128 := n2_val256_v_lt_pow128 v0 v1
  set out := iterN2V5 false v0 v1 0 0 u0 u1 u2 0 0 with hout
  have key : val256 out.2.1 out.2.2.1 out.2.2.2.1 out.2.2.2.2.1 +
      out.2.2.2.2.2.toNat * 2^256 < 2^128 := by omega
  refine ⟨?_, ?_, ?_⟩
  · have : out.2.2.2.1.toNat = 0 := by simp only [EvmWord.val256] at key; omega
    exact BitVec.eq_of_toNat_eq (by rw [this]; rfl)
  · have : out.2.2.2.2.1.toNat = 0 := by simp only [EvmWord.val256] at key; omega
    exact BitVec.eq_of_toNat_eq (by rw [this]; rfl)
  · have : out.2.2.2.2.2.toNat = 0 := by simp only [EvmWord.val256] at key; omega
    exact BitVec.eq_of_toNat_eq (by rw [this]; rfl)

/-- **Combined clean 2-limb Euclidean step for the v5 n=2 max path.** -/
theorem iterN2V5_false_step
    (v0 v1 u0 u1 u2 : Word) (hbnz : v0 ||| v1 ||| 0 ||| 0 ≠ 0)
    (hv1 : v1.toNat ≥ 2^63) (hbltu : ¬ BitVec.ult u2 v1)
    (hvalid : val256 u0 u1 u2 0 < 2^64 * val256 v0 v1 0 0) :
    val256 u0 u1 u2 0 =
      (iterN2V5 false v0 v1 0 0 u0 u1 u2 0 0).1.toNat * val256 v0 v1 0 0 +
        ((iterN2V5 false v0 v1 0 0 u0 u1 u2 0 0).2.1.toNat +
          2^64 * (iterN2V5 false v0 v1 0 0 u0 u1 u2 0 0).2.2.1.toNat) ∧
      (iterN2V5 false v0 v1 0 0 u0 u1 u2 0 0).2.1.toNat +
          2^64 * (iterN2V5 false v0 v1 0 0 u0 u1 u2 0 0).2.2.1.toNat <
        val256 v0 v1 0 0 := by
  obtain ⟨hc2, hc3, hco⟩ := iterN2V5_false_remainder_collapse v0 v1 u0 u1 u2 hbnz hv1 hbltu hvalid
  have hconv := iterN2V5_false_conservation v0 v1 u0 u1 u2 hbnz hv1 hbltu
  have hlt := iterN2V5_false_remainder_lt v0 v1 u0 u1 u2 hbnz hv1 hbltu hvalid
  set out := iterN2V5 false v0 v1 0 0 u0 u1 u2 0 0 with hout
  have h0 : (0 : Word).toNat = 0 := rfl
  have hcollapse : val256 out.2.1 out.2.2.1 out.2.2.2.1 out.2.2.2.2.1 =
      out.2.1.toNat + 2^64 * out.2.2.1.toNat := by
    rw [hc2, hc3]; simp only [EvmWord.val256, h0]; ring
  constructor
  · rw [hconv, hcollapse, hco, h0]; ring
  · rw [hcollapse] at hlt; rw [hco, h0] at hlt; simpa using hlt

/-- **Unified per-digit step (both branches).** For any `bltu` correctly
    reflecting the comparison `u2 < v1`, with the window-validity invariant
    `val256 window < 2^64·val256 v`, the digit produces the clean 2-limb
    Euclidean step `val256 window = q·val256 v + R` with `R < val256 v`.
    Dispatches to `iterN2V5_true_step` (call) or `iterN2V5_false_step` (max).
    One lemma per digit for the cross-digit `fullDivN2MulSubEqV5` assembly. -/
theorem iterN2V5_step (bltu : Bool) (v0 v1 u0 u1 u2 : Word)
    (hbnz : v0 ||| v1 ||| 0 ||| 0 ≠ 0)
    (hv1 : v1.toNat ≥ 2^63)
    (hvalid : val256 u0 u1 u2 0 < 2^64 * val256 v0 v1 0 0)
    (hcall : bltu = true → BitVec.ult u2 v1 = true)
    (hmax : bltu = false → ¬ BitVec.ult u2 v1) :
    val256 u0 u1 u2 0 =
      (iterN2V5 bltu v0 v1 0 0 u0 u1 u2 0 0).1.toNat * val256 v0 v1 0 0 +
        ((iterN2V5 bltu v0 v1 0 0 u0 u1 u2 0 0).2.1.toNat +
          2^64 * (iterN2V5 bltu v0 v1 0 0 u0 u1 u2 0 0).2.2.1.toNat) ∧
      (iterN2V5 bltu v0 v1 0 0 u0 u1 u2 0 0).2.1.toNat +
          2^64 * (iterN2V5 bltu v0 v1 0 0 u0 u1 u2 0 0).2.2.1.toNat <
        val256 v0 v1 0 0 := by
  cases bltu with
  | true =>
    have hu : u2.toNat < v1.toNat := by
      have := hcall rfl; rw [BitVec.ult] at this; exact of_decide_eq_true this
    exact iterN2V5_true_step v0 v1 u0 u1 u2 hbnz hv1 hu
  | false =>
    exact iterN2V5_false_step v0 v1 u0 u1 u2 hbnz hv1 (hmax rfl) hvalid

end EvmAsm.Evm64
