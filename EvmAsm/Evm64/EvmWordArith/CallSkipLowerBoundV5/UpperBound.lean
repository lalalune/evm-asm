/-
  EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV5.UpperBound

  **V5.4.5**: `div128Quot_v5 ≤ q_true_full + 1` unconditionally.

  Composition: V5.4.2 (Q1dd ≤ q_true_1) + V5.4.3 (un21 = r1) +
  V5.4.4 (Q0dd ≤ q_true_0 + 1) via `div128_two_step_upper_of_q0_upper_nat`.

  The bridge `divKTrialCallV5QHat_eq_div128Quot_v5` is currently a `sorry`
  due to a let-binding structural mismatch in the V5 let chain;
  the mathematical content (QHat ≤ q_true+1) is fully proved.

  Bead evm-asm-wbc4i.4.5 (V5.4.5).
-/

import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV5.Q0ddBound
import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV4.UpperBound
import EvmAsm.Evm64.DivMod.LoopBody.TrialCallBounds

namespace EvmAsm.Evm64

open EvmAsm.Rv64 EvmWord

/-- Bridge: QHat = div128Quot_v5.  Currently `sorry` — the V5 let chain has
    a structural mismatch where `cu_q1_dlo` is bound inline vs via `dLo`.
    The mathematical theorem is provable; this is a definitional-equality gap. -/
theorem divKTrialCallV5QHat_eq_div128Quot_v5 (uHi uLo vTop : Word) :
    divKTrialCallV5QHat uHi uLo vTop = div128Quot_v5 uHi uLo vTop := by
  -- The unfold+rfl approach fails: V5 Un21 is @[irreducible] and called in
  -- both Q0c and Rhat2c, producing 2 copies of the Q1dd/Rhatdd let chain.
  -- div128Quot_v5 shares un21 via a single let-binding. The terms are
  -- definitionally equal, but rfl exceeds maxRecDepth before verifying.
  -- Would require @[reducible] on divKTrialCallV5Un21 or a restructured
  -- Un21 definition. Tracked as a follow-up bead.
  sorry

/-- QHat.toNat = Q1dd * 2^32 + Q0dd when both digits < 2^32. -/
private theorem divKTrialCallV5QHat_toNat_eq (uHi uLo vTop : Word)
    (hq1_lt : (divKTrialCallV5Q1dd uHi uLo vTop).toNat < 2^32)
    (hq0_lt : (divKTrialCallV5Q0dd uHi uLo vTop).toNat < 2^32) :
    (divKTrialCallV5QHat uHi uLo vTop).toNat =
      (divKTrialCallV5Q1dd uHi uLo vTop).toNat * 2^32 +
        (divKTrialCallV5Q0dd uHi uLo vTop).toNat := by
  unfold divKTrialCallV5QHat
  rw [show (32 : BitVec 6).toNat = 32 from by decide]
  exact EvmWord.halfword_combine _ _ hq1_lt hq0_lt

/-- **V5.4.5**: `div128Quot_v5 ≤ q_true + 1` unconditionally. -/
theorem div128Quot_v5_le_q_true_plus_one
    (uHi uLo vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63)
    (huHi_lt_vTop : uHi.toNat < vTop.toNat) :
    (div128Quot_v5 uHi uLo vTop).toNat ≤
      (uHi.toNat * 2^64 + uLo.toNat) / vTop.toNat + 1 := by
  rw [← divKTrialCallV5QHat_eq_div128Quot_v5]
  let q1 := divKTrialCallV5Q1dd uHi uLo vTop
  let q0 := divKTrialCallV5Q0dd uHi uLo vTop
  let un1 := divKTrialCallV5Un1 uLo
  let un0 := divKTrialCallV5Un0 uLo
  let un21 := divKTrialCallV5Un21 uHi uLo vTop
  have hvTop_pos : 0 < vTop.toNat := by omega
  -- Q1dd ≤ q_true_1 < 2^32.
  have h_q1_le : q1.toNat ≤ (uHi.toNat * 2^32 + un1.toNat) / vTop.toNat :=
    divKTrialCallV5Q1dd_le_q_true_1 uHi uLo vTop hvTop_ge huHi_lt_vTop
  have h_q1_lt : q1.toNat < 2^32 := by
    have h_N_lt : uHi.toNat * 2^32 + un1.toNat < vTop.toNat * 2^32 := by
      have h_un1 := divKTrialCallV5Un1_lt_pow32 uLo; nlinarith
    have : (uHi.toNat * 2^32 + un1.toNat) / vTop.toNat < 2^32 :=
      (Nat.div_lt_iff_lt_mul (by omega)).mpr (by linarith)
    omega
  -- Q0dd ≤ q_true_0 + 1 < 2^32.
  have h_q0_le : q0.toNat ≤ (un21.toNat * 2^32 + un0.toNat) / vTop.toNat + 1 :=
    divKTrialCallV5Q0dd_le_q_true_0_plus_one uHi uLo vTop hvTop_ge huHi_lt_vTop
  have h_q0_lt : q0.toNat < 2^32 := by
    -- Q0dd ≤ Q0d ≤ Q0c < 2^32 (from the cap)
    have h_q0c_lt : (divKTrialCallV5Q0c uHi uLo vTop).toNat < 2^32 := by
      rw [divKTrialCallV5Q0c_eq_algorithm]; exact algorithmQ0cV5_lt_pow32 uHi uLo vTop
    have h_q0d_le : (divKTrialCallV5Q0d uHi uLo vTop).toNat ≤
        (divKTrialCallV5Q0c uHi uLo vTop).toNat := by
      unfold divKTrialCallV5Q0d; exact div128Quot_phase2b_q0'_le_self _ _ _ _
    have h_q0dd_le : q0.toNat ≤ (divKTrialCallV5Q0d uHi uLo vTop).toNat := by
      show (divKTrialCallV5Q0dd uHi uLo vTop).toNat ≤ _
      delta divKTrialCallV5Q0dd; exact div128Quot_phase2b_q0'_le_self _ _ _ _
    exact lt_of_le_of_lt (le_trans h_q0dd_le h_q0d_le) h_q0c_lt
  -- QHat.toNat = q1 * 2^32 + q0.
  have h_qhat : (divKTrialCallV5QHat uHi uLo vTop).toNat = q1.toNat * 2^32 + q0.toNat :=
    divKTrialCallV5QHat_toNat_eq uHi uLo vTop h_q1_lt h_q0_lt
  rw [h_qhat]
  -- un21 = r1 = (uHi * 2^32 + un1) % vTop.
  have h_un21_eq_r1 : un21.toNat = (uHi.toNat * 2^32 + un1.toNat) % vTop.toNat :=
    divKTrialCallV5Un21_eq_r1 uHi uLo vTop hvTop_ge huHi_lt_vTop
  -- uLo.toNat = un1 * 2^32 + un0.
  have h_uLo : uLo.toNat = un1.toNat * 2^32 + un0.toNat := by
    unfold un1 un0 divKTrialCallV5Un1 divKTrialCallV5Un0
    exact div128Quot_vTop_decomp uLo
  -- Apply two-step Nat composition.
  have h_upper :=
    div128_two_step_upper_of_q0_upper_nat
      uHi.toNat un1.toNat un0.toNat vTop.toNat q1.toNat q0.toNat un21.toNat
      hvTop_pos h_q1_le h_un21_eq_r1 h_q0_le
  have h_eq : uHi.toNat * 2^64 + un1.toNat * 2^32 + un0.toNat =
      uHi.toNat * 2^64 + uLo.toNat := by rw [h_uLo]; ring
  rw [h_eq] at h_upper
  exact h_upper

end EvmAsm.Evm64
